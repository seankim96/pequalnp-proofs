# L-meta-2625: replacing dominated gates

Parent `4cf3d1bdd26cb9414e7e046edf7b33a864fec81f`. Upstream `aecf602ea3c8da01533a13d2ca03b633689f3033`, pinned Lean 4.36.0. The desk returned `not_open` for this unit and no scoped assignment. No lease was acquired. Four existing account PRs were closed, the fork had 28 branches before this work, and PRs #7762 and #8170 were merged with accepted checks and no pending review changes. Upstream still contained reductions 50, 317 and 487 for this unit.

## Excluding the whole previous AND(0,1) branch at h = 28

Use the first ten gates from the parent: OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24), AND(15,32), AND(25,32). Here h counts suffix ANDs explicitly reading wire 32 after gate eight.

Compare a non-guard gate g with a physical guard AND k available at the same position. On every positive row where g is true, require k to be true. On every negative row where k is true, require g to be true. Replacing g by k improves the intermediate wire in the appropriate direction on each row. Because the suffix uses monotone gates, this preserves separation at the original output, at the same size, and increases h by one.

`PlaneCase35DominatingGuard` proves size ≥ 36+h whenever such a replacement exists, given the previously checked size ≥ 35+h theorem. Its prefix after gate eight, the position of the replaced gate, and the remaining suffix are arbitrary. At gate 11, AND(0,1) fires on zero positive and 27 negative rows. AND(19,32) fires on zero positive and only two of those negatives. Lean certifies this comparison in `and01Witness`. The previous two fixed guard reads leave at least 26 in the tail when h ≥ 28. Thus every separating circuit on this branch has size ≥64. This closes all 1,406 twelfth-gate continuations at this boundary. The parent had obtained 262 individual numerical exclusions within this branch.

The concrete theorem was independently composed in pinned Lean as `PlaneCase35DominatingGuard.and01Bound PlaneCase35RescuedGuardSize`. Its conclusion is 64 ≤ 11 + tail.length, and its remaining assumptions are separation on all rows and at least 26 tail guard reads. Its axiom audit listed only propext, Quot.sound and Classical.choice.

## Normalization without a guard-count assumption

`PlaneGuardNormalization` starts with any fixed pool of wires and any legal separating suffix. Among same-length separators with that pool and output, a representative exists with at least as many guard reads and no replaceable non-guard gate. The proof inducts on the number of non-guard gates. Each replacement preserves legal operand indices and the output requirements. This theorem can discard representatives in an existence search at every h when h is free. It does not say that each discarded configuration is itself impossible.

The implementation only removes free gates built from fixed wire values for which a legal replacement is known. It never normalizes an already fixed gate. The separate 28-read option can rule out fixed gates using the size theorem. Replay the finite counts with `python research/order3_case35_dominance_replay.py`. For each gate reported as dominated the script independently evaluates both gates row by row. The Lean certificate explicitly checks AND(0,1). The following aggregate counts are Python results.

| Fixed prefix | Candidate next gates | Dominated by a physical guard AND | Additional exclusions beyond the parent interchangeability rule at h=28 | Remaining at h=28 using both rules |
| --- | ---: | ---: | ---: | ---: |
| First 8 | 1,190 | 451 | 346 | 640 |
| First 9 | 1,260 | 487 | 365 | 673 |
| First 10 | 1,332 | 524 | 388 | 707 |
| First 10, then AND(0,17) | 1,406 | 555 | 388 | 738 |

## Solver runs

All attempts synthesized size 63 with unrestricted binary suffix wiring. CEGIS was seeded with positives 0–51 and negatives 0, 1, 2 and 234. The full verification set has 520 rows. The common command is:

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --solver PATH_TO_PINNED_CADICAL
```

| Append to common command | Variables / clauses | Wall limit | Verdict |
| --- | --- | ---: | --- |
| `--ninth AND 15 32 --tenth AND 25 32 --eleventh AND 0 17 --min-guard-reads 28 --semantic-boundary` | 18,460 / 562,986 | 90 s | UNKNOWN |
| Same fixed gates and minimum, using `--dominating-guard` instead of `--semantic-boundary` | 18,460 / 603,338 | 120 s | UNKNOWN |
| `--semantic-budget --normalize-guard` with only the first eight fixed and no minimum guard count | 19,580 / 637,290 | 180 s | UNKNOWN |

All three UNKNOWN runs ended with 56 encoded rows and zero decoded candidates. As a regression test, fixing gate 11 to AND(0,1) with the new dominance rule and a 10-second budget returned UNSAT on the 56 encoded rows (18,460 variables, 536,337 clauses). The rule emits an empty clause for this fixed prefix using a witness evaluated on all 520 rows; the independent mathematical exclusion is the Lean corollary above. The unrestricted 63-gate question has no verdict here. Next: use the 707 surviving gate-11 choices at h=28 or target the 738 surviving gate-12 choices after AND(0,17). A further proof could allow an existing wire that dominates a non-guard gate to replace it by deleting the gate and renumbering its users.

## Verification and delivery

| Theorem | Pinned project checker | Constants rechecked | One-file comparison |
| --- | --- | ---: | --- |
| PlaneCase35DominatingGuard | ACCEPTED (check) | 1,829 | [comparison](https://github.com/seankim96/pequalnp-proofs/compare/aecf602ea3c8da01533a13d2ca03b633689f3033...e2b23188932da70ff5e0d8da51cb2097c2db6fd3) |
| PlaneGuardNormalization | ACCEPTED (check) | 1,736 | [comparison](https://github.com/seankim96/pequalnp-proofs/compare/aecf602ea3c8da01533a13d2ca03b633689f3033...4b1d5c485b41818cf2c08ee5e5dd41716b5260be) |

Both checked manifests include only the respective proof file and 87 unchanged upstream definition modules. Each external statement was also compiled independently. The normalization CNF gate clauses were checked in both operand orders on 2,312, 2,592 and 2,738 configurations with 8, 10 and 11 gates fixed. No upstream PR was submitted for this unleased unit.
