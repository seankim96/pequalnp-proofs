"""Eight-probe density after preloading one non-guard AND or a dominated wire."""
import json
from itertools import combinations_with_replacement
from pathlib import Path

import numpy as np

from order3_case35_colored_trace import constants, family, witness_graph
from order3_case35_first_or import PREFIX13, packing
from order3_case35_semantic_reuse import columns

ROOT=Path(__file__).with_name("results")


def greedy_family(flags,widths):
    conflict=flags==0
    np.fill_diagonal(conflict,False)
    degree=conflict.sum(axis=1)
    active=np.ones(len(flags),dtype=bool)
    chosen=[]
    while active.any():
        i=int(np.argmin(np.where(active,100*degree-widths,1000000)))
        chosen.append(i)
        remove=active & conflict[i]
        remove[i]=True
        active[remove]=False
        degree-=conflict[:,remove].sum(axis=1)
    a,b=np.triu_indices(len(chosen),1)
    if not np.all(flags[np.array(chosen)[a],np.array(chosen)[b]]):
        raise ValueError("invalid family")
    return chosen


def evaluator(pool):
    packs=json.loads((ROOT/"case35-density-packings.json").read_text())
    if len(packs)!=468:
        raise ValueError("expected one packing per physical negative")
    for j,fs in enumerate(packs):
        packing(pool,(j,fs))
    graph=witness_graph(pool)
    widths=np.array(list(map(len,packs)))
    all_pos=(1<<52)-1
    guard_off=[j for j in range(468) if not pool[32]>>(52+j)&1]

    def budget(value, dominated):
        # In the dominated case V can be any column below value. Delete
        # all potentially unsafe positive witnesses and keep at most one
        # potentially active flag per packing, independent of V.
        reduced=graph & np.uint64(all_pos^(value&all_pos))
        off=np.array([not value>>(52+j)&1 for j in range(468)])
        f=reduced if dominated else np.where(off[:,None]&off,reduced,graph)
        K=greedy_family(f,widths)
        k=len(K)
        if k<=160 or not family(f,guard_off,129):
            return k,0
        mass=2*sum(sorted(x.bit_count() for x in range(256))[:k])
        if k<=192:
            mass-=256
        for c in pool+([] if dominated else [value]):
            ones=sum(c>>(52+j)&1 for j in K)
            if max(ones,k-ones)<129 and c not in constants(f,[c]):
                mass-=min(ones,128)
        if dominated and not family(f,np.flatnonzero(off).tolist(),129):
            mass-=min(128,sum(value>>(52+j)&1 for j in K))
        total=0
        for j in K:
            if dominated:
                total+=len(packs[j])-max(0,sum(value>>p&1 for p in packs[j])-1)
            else:
                packing(pool+[value],(j,packs[j]))
                total+=len(packs[j])
        return k,(mass+total+k-1)//k-1

    return budget


def bounds(pool):
    budget=evaluator(pool)
    killed=set()
    summary=[]
    cached={}
    for a,b in combinations_with_replacement(range(39),2):
        if 32 in (a,b):
            continue
        value=pool[a]&pool[b]
        if value not in cached:
            cached[value]=budget(value,False)
        k,r=cached[value]
        summary.append([a,b,k,r])
        if r>19:
            killed.add((a,b))
    dominated=[budget(v,True) for v in pool]
    return killed,summary,dominated


def constrain(model,rows,min_reads):
    if model.size!=63 or min_reads!=24 or model.prefix[:13]!=PREFIX13 or len(rows)!=520:
        raise ValueError("preload density requires 24 guard reads at the case-35 thirteen-gate prefix")
    pool=columns(model.prefix,rows)
    killed,_,dom=bounds(pool[:39])
    # At 24 reads a separator has exactly nine paid ANDs and nineteen ORs:
    # eight paid gates need >=24 ORs by the density bound. Removing any
    # particular paid AND by preloading its value leaves eight paid gates
    # and the same nineteen ORs. The wire is an extra primary input and all
    # other indices are consistently remapped; no OR is spent on a copy.
    from order3_case35_colored_trace import density
    if density(pool[:39],ROOT/"case35-or-trace-density.json")["required_ors"]<=20:
        raise ValueError("missing baseline eight-paid-AND exclusion")
    banned={i for i,v in enumerate(pool) if any(r>19 and v & ~pool[t]==0 for t,(_,r) in enumerate(dom))}
    for op,a,b in model.prefix[13:]:
        if op and 32 not in (a,b) and (a in banned or b in banned or tuple(sorted((a,b))) in killed):
            model.clause()
            return
    for g in model.gates:
        paid=model.fresh()
        model.clause(-g.is_and,g.left[32],g.right[32],paid)
        for i in banned:
            model.clause(-paid,-g.left[i])
            model.clause(-paid,-g.right[i])
        if len(killed)==741:
            model.clause(-paid,*g.left[39:],*g.right[39:])
        else:
            for a,b in killed:
                model.clause(-paid,-g.left[a],-g.right[b])
                model.clause(-paid,-g.left[b],-g.right[a])


if __name__=="__main__":
    from order3_prefix_search import test_rows
    _,summary,dom=bounds(columns(PREFIX13,test_rows()))
    expected=json.loads((ROOT/"case35-density-preload.json").read_text())
    if summary!=expected:
        raise ValueError("preload certificate summary differs")
    print("verified pairs",len(summary),"minimum ORs",min(r for _,_,_,r in summary))
    print("certified dominators",[i for i,(_,r) in enumerate(dom) if r>19])


def verify_sparse(pool):
    from itertools import combinations
    certificate=json.loads((ROOT/"case35-density-sparse.json").read_text())
    expected=[tuple(x) for n in range(3) for x in combinations(range(52),n)]
    if [tuple(ids) for ids,_,_ in certificate]!=expected:
        raise ValueError("sparse certificate does not cover all supports of size at most two")
    evaluate=evaluator(pool)
    # The hypothetical preloaded wire is arbitrary on all 468 negatives.
    # Its only restriction is containment on positives in the stated mask.
    negatives=((1<<468)-1)<<52
    for ids,k,r in certificate:
        mask=negatives | sum(1<<i for i in ids)
        if evaluate(mask,True)!=(k,r) or r<=19:
            raise ValueError("sparse support budget did not exclude the preloaded gate")
    return len(expected)


def constrain_sparse(model,rows,min_reads,positives):
    if model.size!=63 or min_reads!=24 or model.prefix[:13]!=PREFIX13 or len(rows)!=520 or len(positives)!=52:
        raise ValueError("sparse density requires 24 reads, the thirteen gates and all positive rows encoded")
    pool=columns(model.prefix,rows)
    verify_sparse(pool[:39])
    for k,(op,a,b) in enumerate(model.prefix[13:],39):
        if op and 32 not in (a,b) and (pool[k]&((1<<52)-1)).bit_count()<3:
            model.clause()
            return
    for k,g in enumerate(model.gates):
        start=len(model.clauses)
        model.require_at_least([w[len(pool)+k] for w in positives],3)
        model.clauses[start:]=[c+(-g.is_and,g.left[32],g.right[32]) for c in model.clauses[start:]]
