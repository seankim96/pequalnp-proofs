"""Eight paid ANDs need sixteen distinct OR parents at the 25-read boundary."""
import numpy as np

from order3_case35_first_or import PREFIX13
from order3_case35_semantic_reuse import columns


def witness_graph(pool):
    """A nonzero mask gives every positive witness for this pair of negatives."""
    words = np.array([sum(((v >> r) & 1) << i for i,v in enumerate(pool))
                      for r in range(520)],dtype=np.uint64)
    neg = words[52:]
    covered = neg[:,None] | neg
    guard = (neg & (1 << 32)) != 0
    flags = np.zeros(covered.shape,dtype=np.uint64)
    for f,x in enumerate(words[:52]):
        safe = (covered & x) == x
        if x & (1 << 32):
            safe &= guard[:,None] & guard
        flags |= safe.astype(np.uint64) << f
    return flags


def family(flags, rows, minimum):
    # Greedy construction is heuristic; the returned certificate is checked
    # against every pair, and a failure to find a family imposes no constraint.
    if len(rows) < minimum:
        return []
    conflict = flags[np.ix_(rows,rows)] == 0
    np.fill_diagonal(conflict,False)
    active = np.ones(len(rows),dtype=bool)
    degree = conflict.sum(axis=1)
    result = []
    while active.any() and len(result)<minimum:
        i = int(np.argmin(np.where(active,degree,10000)))
        result.append(rows[i])
        removed = active & conflict[i]
        removed[i] = True
        active[removed] = False
        degree -= conflict[:,removed].sum(axis=1)
    if len(result)<minimum:
        return []
    a,b = np.triu_indices(len(result),1)
    chosen = np.array(result)
    if not np.all(flags[chosen[a],chosen[b]]):
        raise ValueError("negative pair has no positive witness")
    return result


def constants(flags, wires):
    cache = {}
    for v in set(wires):
        for bit in (0,1):
            rows = [i for i in range(468) if (v >> (52+i) & 1) == bit]
            K = family(flags,rows,129)
            if K:
                cache[v] = bit,K
                break
    return cache


def classify(prefix, rows):
    if prefix[:13] != PREFIX13 or len(rows)!=520:
        raise ValueError("requires all 520 rows and the exact 13-gate prefix")
    pool = columns(prefix,rows)
    flags = witness_graph(pool[:39])
    if not family(flags,list(range(468)),193):
        raise ValueError("need 193 pairwise distinguishable negatives")
    cert = constants(flags,pool)
    if any(v not in cert for v in pool[:39]):
        raise ValueError("missing physical input certificate")
    # Every future guard AND vanishes throughout this particular family.
    if not family(flags,[i for i in range(468) if not pool[32] >> (52+i) & 1],129):
        raise ValueError("missing guard-false family")
    return pool,cert


def constrain(model, rows, min_reads):
    if model.size!=63 or min_reads!=25:
        raise ValueError("colored trace cuts are for size 63 and at least 25 guard reads")
    pool,cert = classify(model.prefix,rows)
    # 19 ORs and 23 guard reads after slot 13 leave exactly eight paid ANDs.
    # Each of their 16 operands must be a distinct OR wire: raw/guard wires
    # are constant on a 129-family. Repeated probes give at most 128 traces.
    # A paid AND output and either of its operands give at most three ordered
    # bit patterns, hence at most 3*64 traces on a 193-family. Equal operands
    # in the same gate make it a copy that needs no trace bit.
    used = set()
    eligible = {i for i in range(39,len(pool)) if not model.prefix[i-26][0] and pool[i] not in cert}
    for op,a,b in model.prefix[13:]:
        if op and 32 not in (a,b):
            if a==b or {a,b} & used or not {a,b} <= eligible:
                model.clause()
                return
            used.update((a,b))
    fixed_or_count = sum(not g[0] for g in model.prefix[13:])
    if fixed_or_count-len(eligible)>3:
        model.clause()
        return
    # Each true arena literal represents use of this wire in one operand slot.
    # Enforce at most one such use per physical wire with a prefix OR.
    seen = {}
    for g in model.gates:
        paid = model.fresh()
        model.clause(-g.is_and,g.left[32],g.right[32],paid)
        for side in (g.left,g.right):
            model.clause(-paid,*(v for i,v in enumerate(side) if i>=len(pool) or i in eligible-used))
            for i,sel in enumerate(side):
                if i<len(pool) and i not in eligible-used:
                    continue
                if i>=len(pool):
                    model.clause(-paid,-sel,-model.gates[i-len(pool)].is_and)
                live = model.fresh()
                model.clause(-paid,-sel,live)
                if i in seen:
                    model.clause(-live,-seen[i])
                    marked=model.fresh()
                    model.clause(-live,marked)
                    model.clause(-seen[i],marked)
                    live=marked
                seen[i]=live
    # Any witness has a one-hot encoding in which the sixteen OR parents
    # can all be selected. At least this many future ORs are therefore needed.
    need=max(0,16-len(eligible))
    if need>len(model.gates):
        model.clause()
    elif need:
        model.require_at_least([-g.is_and for g in model.gates],need)


def density(pool,certificate_path):
    """Derive a minimum OR count when exactly eight non-guard ANDs remain."""
    import json
    from pathlib import Path
    from order3_case35_first_or import packing
    cert = json.loads(Path(certificate_path).read_text())
    K = [j for j,_ in cert]
    if len(set(K)) != len(K) or not 160 < len(K) <= 256:
        raise ValueError("invalid negative family for eight probes")
    flags = witness_graph(pool)
    a,b = np.triu_indices(len(K),1)
    endpoints=np.array(K)
    if not np.all(flags[endpoints[a],endpoints[b]]):
        raise ValueError("two negatives lack a positive witness")
    widths = 0
    for c in cert:
        packing(pool,c)
        widths += len(c[1])
    # A paid gate input cannot be constant on any 129-witness family.
    # Count each exceptional initial wire at most once across the 16 ports.
    constant=constants(flags,pool)
    initial=[i for i,v in enumerate(pool) if v not in constant]
    if not family(flags,[i for i in range(468) if not pool[32]>>(52+i)&1],129):
        raise ValueError("cannot eliminate future mask AND outputs")
    # Selecting an earlier paid gate as probe gives a bit bounded by an input
    # bit of that earlier gate. Two distinct receiving gates give two such
    # inequalities simultaneously, choosing orientations along the DAG.
    # One implication leaves <=192 codes; two leave <=160 (including chains,
    # shared source and disjoint implications). Thus at most two paid-output
    # ports survive for 161..192 rows, both in one receiving gate.
    paid_ports=0 if len(K)>192 else 2
    # Each orientation is injective, so its total population count is at
    # least that of the |K| lightest eight-bit words. Apply to both sides.
    weight=2*sum(sorted(x.bit_count() for x in range(256))[:len(K)])
    # Each single probe is true on at most 128 rows (eight-bit injectivity).
    non_or_weight=128*paid_ports + sum(min(128,sum((pool[i]>>(52+j))&1 for j in K)) for i in initial)
    minimum_or_ones=weight-non_or_weight
    required=(minimum_or_ones+widths+len(K)-1)//len(K)-1
    return dict(rows=len(K),widths=widths,raw_exceptions=initial,paid_ports=paid_ports,
                minimum_or_ones=minimum_or_ones,required_ors=required)


def constrain_density(model,rows,min_reads):
    from pathlib import Path
    if model.size!=63 or model.prefix[:13]!=PREFIX13 or len(rows)!=520:
        raise ValueError("density requires the full target and exact thirteen-gate prefix")
    paths=Path(__file__).with_name("results")
    cases=[(13,"case35-or-trace-density.json",19)]
    for a,b,minimum in [(13,19,18),(14,18,19)]:
        if model.prefix[13:15]==((False,a,b),(True,1,39)):
            cases.append((15,f"case35-density-after-{a}.json",minimum))
    for cut,name,or_floor in cases:
        pool=columns(model.prefix[:cut],rows)
        result=density(pool,paths/name)
        # For the 14,18 subtree at this cut the residual 19-OR floor uses
        # the prior full recursive packing certificate, independently replayed.
        if cut==15 and model.prefix[13][1]==14:
            from order3_case35_first_or import replay_branch_tree
            replay_branch_tree(pool[:39])
        # The base 19-OR theorem after gate 7 implies 18 after the fixed OR.
        fixed=model.prefix[cut:]
        before_reads=sum(op and 32 in (a,b) for op,a,b in model.prefix[7:cut])
        available=model.size-cut-max(0,min_reads-before_reads)
        if 9+or_floor>available and 8+result["required_ors"]>available:
            model.clause()
            return
        # Valid disjunction: at least nine paid ANDs, or >= R ORs. Count
        # free slots with Boolean witnesses for the selected branch.
        paid=[];ors=[]
        for g in model.gates:
            mark=model.fresh()
            model.clause(-mark,g.is_and)
            model.clause(-mark,-g.left[32])
            model.clause(-mark,-g.right[32])
            paid.append(mark)
            ors.append(-g.is_and)
        choice=model.fresh()
        for literals,needed,guard in [
            (paid,9-sum(op and 32 not in (a,b) for op,a,b in fixed),choice),
            (ors,result["required_ors"]-sum(not op for op,a,b in fixed),-choice)]:
            if needed>len(literals):
                model.clause(guard)
            elif needed>0:
                start=len(model.clauses)
                model.require_at_least(literals,needed)
                model.clauses[start:]=[c+(guard,) for c in model.clauses[start:]]


if __name__=="__main__":
    from pathlib import Path
    from order3_prefix_search import test_rows
    root=Path(__file__).with_name("results")
    for gates,name in [((),"case35-or-trace-density.json"),
                       (((False,14,18),(True,1,39)),"case35-density-after-14.json"),
                       (((False,13,19),(True,1,39)),"case35-density-after-13.json")]:
        print(gates,density(columns(PREFIX13+gates,test_rows()),root/name))
