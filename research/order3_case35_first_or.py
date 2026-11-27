"""Replay the first-OR packing certificates and the two gate-15 negative trace covers."""
import json
from functools import lru_cache
from itertools import combinations
from pathlib import Path

from order3_case35_semantic_reuse import PREFIX, columns

PREFIX13 = PREFIX + ((True, 0, 17), (True, 0, 23), (True, 0, 25))
POS = (1 << 52) - 1
CERT = Path(__file__).with_name("results") / "case35-first-or-traces.json"


def packing(pool, certificate):
    j, flags = certificate
    if not (0 <= j < 468 and len(flags) == len(set(flags)) and all(0 <= f < 52 for f in flags)):
        raise ValueError("invalid flag packing")
    mask = sum(1 << f for f in flags)
    if any(not c >> (52+j) & 1 and (c & mask).bit_count() > 1 for c in pool):
        raise ValueError("a generator hits multiple selected flags while false on the negative")
    return j, mask


def replay_first(pool, certificates):
    if any(len(flags) != 19 for _, flags in certificates):
        raise ValueError("expected nineteen flags per packing")
    tests = [packing(pool[:33], certificate) for certificate in certificates]
    closure = {(1 << 520) - 1}
    for generator in pool[:33]:
        closure |= {v & generator for v in closure}
    hard = {v for v in closure if all(not v >> (52+j) & 1 and v & mask for j, mask in tests)}
    if hard != {pool[13], pool[19]}:
        raise ValueError("exceptional conjunctions differ from the two line columns")
    return len(closure)


def replay_after_or(pool, branch):
    """Each pair of negatives needs a positive witness even with the extra AND output."""
    a, b = branch["first_or"]
    cols = pool + [pool[a] | pool[b]]
    packing(cols, branch["packing"])
    positives, negatives = [], []
    for row in range(520):
        word = sum(((col >> row) & 1) << i for i, col in enumerate(cols))
        (positives if row < 52 else negatives).append(word)

    @lru_cache(None)
    def witnesses(i, j):
        x, y = negatives[i], negatives[j]
        return sum(1 << f for f, z in enumerate(positives)
                   if not z & ~(x | y) and (not z & (1 << 32) or x & y & (1 << 32)))

    expected = {40*i+j for i in range(40) for j in range(i,40) if 32 not in (i,j)}
    classified = set()
    for group in branch["groups"]:
        family = group["negatives"]
        if len(set(family)) < 129 or len(set(family)) != len(family) or min(family) < 0 or max(family) >= 468:
            raise ValueError("invalid negative trace family")
        pairs = [(negatives[i], negatives[j], witnesses(i,j)) for i,j in combinations(family,2)]
        if any(not flags for _, _, flags in pairs):
            raise ValueError("initial pool has an unseparated pair")
        for code in group["codes"]:
            if code not in expected or code in classified:
                raise ValueError("unexpected or duplicate AND")
            i, j = divmod(code,40)
            operands = (1 << i) | (1 << j)
            active = cols[i] & cols[j] & POS
            if any(not flags & ~active and x & operands != operands and y & operands != operands
                   for x,y,flags in pairs):
                raise ValueError("new AND destroys all witnesses for a pair")
            classified.add(code)
    if classified != expected:
        raise ValueError("missing non-guard ANDs")
    return len(classified)


def constrain(model, rows, min_reads):
    if model.size != 63 or model.prefix[:13] != PREFIX13 or len(rows) != 520:
        raise ValueError("first-OR bounds require the certified 13 gates and all 520 tests")
    cert = json.loads(CERT.read_text())
    pool = columns(model.prefix, rows)
    replay_first(pool[:39], cert["packings"])
    extra = model.prefix[13:]
    first = next((g for g in extra if not g[0]), None)
    if first:
        _, a, b = first
        pair = {pool[a] & POS, pool[b] & POS}
        if pair != {pool[13] & POS, pool[19] & POS} and min_reads >= 26:
            model.clause()
            return
    elif min_reads >= 26:
        # Before the first OR, a column can contain all four incident flags of
        # a line only if both parents contain them. Track each side separately.
        # A complete circuit always has a one-hot selector representation.
        from order3_prefix_search import negate
        may = [[col & bits == bits for col in pool] for bits in (pool[13] & POS, pool[19] & POS)]
        prior_or = False
        for gate in model.gates:
            left = [model.operand(gate.left, side) for side in may]
            right = [model.operand(gate.right, side) for side in may]
            # (L13 & R19) | (L19 & R13), conditioned on being the first OR.
            for x in (left[0], right[1]):
                for y in (left[1], right[0]):
                    model.clause(prior_or, gate.is_and, x, y)
            for k in range(2):
                contains = model.fresh()
                model.clause(-contains, -gate.is_and, left[k])
                model.clause(-contains, -gate.is_and, right[k])
                may[k].append(contains)
            seen = model.fresh()
            model.clause(-seen, prior_or, -gate.is_and)
            model.clause(negate(prior_or), seen)
            model.clause(gate.is_and, seen)
            prior_or = seen
    # Just after a specified first OR, an additional non-guard AND in position
    # 15 still leaves eight paid ANDs and (packing size minus one) ORs to pay.
    if not extra or extra[0][0]:
        return
    branch = next((c for c in cert["branches"] if tuple(c["first_or"]) == extra[0][1:]), None)
    if branch is None or 15 + 8 + len(branch["packing"][1]) - 1 + max(0,min_reads-2) <= 63:
        return
    replay_after_or(pool[:39], branch)
    if len(extra) == 1:
        gate = model.gates[0]
        model.clause(-gate.is_and, gate.left[32], gate.right[32])
    elif extra[1][0] and 32 not in extra[1][1:]:
        model.clause()


def replay_second(pool, certificates):
    augmented = pool[:33] + [pool[13] | pool[19]]
    tests = [packing(augmented, c) for c in certificates]
    if not tests or any(len(flags) != 18 for _, flags in certificates):
        raise ValueError("expected eighteen flags per second-stage packing")
    for index in (13, 19):
        # Therefore any AND-only wire matching the line must be identical
        # to the original input, including on the negative rows.
        bits = pool[index] & POS
        if [i for i, c in enumerate(pool[:33]) if c & bits == bits] != [index]:
            raise ValueError("a line signature can come from another generator")
    closure = {(1 << 520) - 1}
    for generator in augmented:
        closure |= {v & generator for v in closure}
    if any(all(not v >> (52+j) & 1 and v & mask for j, mask in tests) for v in closure):
        raise ValueError("second-stage closure has an exceptional conjunction")
    return len(closure)


def constrain_ceiling(model, rows, min_reads):
    if model.size != 63 or model.prefix[:13] != PREFIX13 or len(rows) != 520:
        raise ValueError("guard ceiling requires size 63, all tests and the exact thirteen-gate prefix")
    cert = json.loads(CERT.read_text())
    pool = columns(PREFIX13,rows)
    replay_first(pool,cert["packings"])
    replay_second(pool,cert["second_packings"])
    extra = model.prefix[13:]
    if min_reads >= 26:
        model.clause()
        return
    needed = max(0,19 - sum(not g[0] for g in extra))
    if needed > len(model.gates):
        model.clause()
        return
    if needed:
        model.require_at_least([-g.is_and for g in model.gates],needed)
    if min_reads == 25:
        # Preloading any physical non-guard pair among the initial 39 wires
        # still costs eight other ANDs. The 19 OR bound is on the original DAG.
        from order3_case35_thirteen_gate_trace import verify_fourteenth
        verify_fourteenth(rows)
        if any(op and 32 not in (a,b) and max(a,b) < 39 for op,a,b in extra):
            model.clause()
            return
        for g in model.gates:
            model.clause(-g.is_and,g.left[32],g.right[32],*g.left[39:],*g.right[39:])
        # After either specified first OR the remaining DAG needs 18 ORs.
        # The 129-negative families still need eight other ANDs after gate 15.
        for branch in cert["branches"]:
            if extra and extra[0] == (False,*branch["first_or"]):
                replay_after_or(pool,branch)
                if len(extra) == 1:
                    g = model.gates[0]
                    model.clause(-g.is_and,g.left[32],g.right[32])
                elif extra[1][0] and 32 not in extra[1][1:]:
                    model.clause()


def replay_or_tree(generators, required, node, counts):
    """Prove an OR bound from an AND-closed initial pool, using only integer bit sets."""
    counts[required] = counts.get(required, 0) + 1
    if "direct" in node:
        if len(node["direct"][1]) != required + 1:
            raise ValueError("direct leaf has the wrong width")
        packing(generators, node["direct"])
        return
    tests = [packing(generators, c) for c in node["packings"]]
    if not tests or any(len(flags) != required for _, flags in node["packings"]):
        raise ValueError("missing or wrongly sized OR packing")
    closure = {(1 << 520) - 1}
    for gen in generators:
        closure |= {v & gen for v in closure}
    hard = [v for v in closure if all(not v >> (52+j) & 1 and v & mask for j,mask in tests)]
    # A first OR containing an easy operand leaves one packing with support
    # at most one on every wire (including the new one). The remaining DAG
    # then costs at least required-1 ORs. Check all pairs not covered this way.
    branches = set()
    for x,y in combinations(sorted(hard),2):
        v = x | y
        if all(not v >> (52+j) & 1 and (v & mask).bit_count() > 1 for j,mask in tests):
            branches.add((x,y))
    for child in node["nodes"]:
        x,y = sorted(int(v,16) for v in child["operands"])
        if (x,y) not in branches:
            raise ValueError("incorrect or duplicated exceptional pair")
        branches.remove((x,y))
        replay_or_tree(generators + [x | y],required-1,child["proof"],counts)
    if branches:
        raise ValueError("packing tree leaves an exceptional first OR unproved")


def replay_branch_tree(pool):
    path = CERT.with_name("case35-or14-18-packing-tree.json")
    counts = {}
    replay_or_tree(pool[:33]+[pool[14] | pool[18]],19,json.loads(path.read_text()),counts)
    return counts


def constrain_branch_tree(model, rows, min_reads):
    if model.size != 63 or len(rows) != 520 or model.prefix[:14] != PREFIX13 + ((False,14,18),):
        raise ValueError("branch packing tree requires its exact fourteen-gate prefix")
    cols = columns(PREFIX13,rows)
    replay_branch_tree(cols)
    # The original trace requires eight non-guard ANDs after gate 13. Gate
    # 14 is an OR. The tree requires 19 more ORs even with its output preloaded.
    if min_reads >= 25:
        model.clause()
        return
    remaining = max(0,19 - sum(not g[0] for g in model.prefix[14:]))
    if remaining > len(model.gates):
        model.clause()
        return
    if remaining:
        model.require_at_least([-g.is_and for g in model.gates],remaining)
    if min_reads == 24:
        branch = next(c for c in json.loads(CERT.read_text())["branches"] if c["first_or"] == [14,18])
        replay_after_or(cols,branch)
        if len(model.prefix) == 14:
            g = model.gates[0]
            model.clause(-g.is_and,g.left[32],g.right[32])
        elif model.prefix[14][0] and 32 not in model.prefix[14][1:]:
            model.clause()


if __name__ == "__main__":
    from order3_prefix_search import test_rows
    cols = columns(PREFIX13, test_rows())
    cert = json.loads(CERT.read_text())
    print("Full conjunction closure:", replay_first(cols, cert["packings"]))
    print("Augmented closure:", replay_second(cols, cert["second_packings"]))
    for branch in cert["branches"]:
        print("OR", branch["first_or"], "verified gate-15 non-guard ANDs:",
              replay_after_or(cols,branch), "packing size:", len(branch["packing"][1]))
    print("OR(14,18) verified tree nodes by residual OR bound:", replay_branch_tree(cols))
