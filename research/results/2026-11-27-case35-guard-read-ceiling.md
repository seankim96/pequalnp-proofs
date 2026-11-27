# L-meta-2625 — case 35, the 25-read frontier

Started from research commit `a2bcabbec092a88d520411be23cf7aad877803f1` on 2026-11-27. Upstream was `b1e52587103ee0bdf02e33aa440ec416e02f60d3`. The account had four closed PRs and 35 fork branches before this session. #7762 and #8170 were merged with ACCEPTED checker comments and no requested revisions. The desk returned `not_open` for this unit and no assignment or lease on its scoped next call. Upstream contained the three reductions 50, 317 and 487. No unrestricted 63-gate result was located. This work is on the fork.

## Kernel-checked statements

Both files are standalone against the upstream commit. See `research/statements` for the expanded types. Gate numbers below start at 1; wire indices start at 0. The physical 13-gate prefix is:

```text
OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27),
OR(2,6), AND(1,24), AND(15,32), AND(25,32), AND(0,17), AND(0,23), AND(0,25).
```

Let h count AND gates reading guard wire 32. Gates 9 and 10 already account for two. The previous result required 18 ORs after gate 7. The new theorem `PlaneCase35GuardReadCeiling.Ordinary.afterSeven` requires **19 ORs** after just the first seven gates, with all subsequent AND/OR wiring and the output unrestricted. For the 13-gate prefix, the known negative trace bound requires eight non-guard ANDs in its suffix. The new exported theorem gives **suffix length ≥ 27 + suffix guard reads**, hence **total size ≥ 38 + h**. Size at most 63 now requires **h ≤ 25**. At size 63 and h=25 the remaining 50 slots must contain exactly eight non-guard ANDs, 19 ORs, and 23 guard ANDs.

1. After gate 7, form all intersections of the input columns on the 520 test rows. Eight packings each choose one negative and 19 distinct positive flags. If a generator is false on the negative, it hits at most one selected flag. This property survives AND. A binary OR can increase the support accounting by at most one. A separator has to hit all of the flags and be false on the chosen negative.
2. Every AND-only column except the signatures of lines 13 and 19 has a packing in which it is true on the negative or false on every chosen flag. If it is an operand of the first OR, the union is still small on that packing; at least 18 *additional* ORs are needed. Equal signatures are handled by idempotence. The intermediate theorem `PlaneCase35FirstOrLines` captures this case, including any number of ANDs before the first OR. A separate Lean specialization checked all 779 nonexceptional ordered-by-index physical OR choices in gate 14.
3. For the exceptional pair, only the raw line input in the original 33-wire pool contains all four positive flags of that line. Induction over ANDs shows that a matching column equals the raw input on **every** row. Preload their union. Eight further packings each use 18 positive flags. Every AND-only column in the enlarged pool has a packing in which it is true on the negative or misses every selected flag. Thus its first subsequent OR is small for a suitable packing, and a further 17 ORs are necessary. Including both ORs yields the claimed 19.
4. The first and second kernel tables contain 135 and 139 projected signatures. The independent scalar replay enumerates 10,180 and 10,541 distinct full 520-row intersections, respectively (including the empty conjunction). The kernel also checks the 131-negative trace bound used to count the eight non-guard ANDs separately.

## Further finite reductions, checked in Python

Run `python research/order3_case35_first_or.py`. The following are independently replayable finite applications. The two Lean files above contain the general first-OR and 25-read bounds; the Python packing tree and the gate-15 trace classifications have not been promoted to standalone Lean statements.

- After either gate 14 = OR(14,18) or OR(13,19), all 780 unordered non-guard ANDs in gate 15 still leave at least eight *additional* non-guard ANDs. For each AND the verifier checks a supplied family of at least 129 negatives. Every pair has a positive flag covered by the two negative endpoints on every available physical column, including the new conjunction, with the free guard condition enforced on both endpoints. All 780 codes in each orientation are checked, including repeated operands and ANDs reading the new wire. With the global 19-OR bound, both branches at h=25 therefore exclude every non-guard AND in gate 15.
- With gate 14 = OR(14,18), preload this result in the original seven-gate pool. The recursive packing certificate in `case35-or14-18-packing-tree.json` demands **19 more ORs**. There are 32 verified nodes: one at residual bound 19, fifteen at 18, and sixteen at 17. The checker exhausts each node's full AND closure, validates each flag packing on all generating columns, and recursively checks every exceptional unordered pair whose OR preserves no packing. An equal-operand OR is covered by idempotence. Enlarging the generators with an exceptional OR allows all preceding ANDs to be regenerated without increasing the OR count. Direct leaves use a packing of size one greater than their claimed lower bound.
- The fixed OR(14,18) prefix therefore has h ≤ 24 at size 63. If gate 15 is *any* non-guard AND, h ≤ 23. In particular the previous run's OR(14,18), AND(1,39) branch is excluded at h=26, 25 **and 24**. The numerical reduction gives no exclusion at h=23.
- The previous preloaded-pair result combines with 19 ORs to give **m + h ≤ 25**, where m is the number of occurrences of any one of the 741 non-guard ANDs on the original 39 wires. At h=25, a non-guard AND must use some newer wire. The encoder applies this for the 25-read boundary after independently replaying the 741 certificates.

## Solver ledger

Pinned Lean 4.36.0's CaDiCaL, size 63. All searches used the full 520-row target; CEGIS initially represented 52 positives and negatives 0, 1, 2 and 234. There were no decoded candidates in any timeout. The UNSAT rows below are regressions with sound structural clauses based on the 520-row target, not independent unsatisfiability proofs using only the 56 encoded rows. Each listed budget is the CEGIS/solver wall budget, excluding certificate replay and model preparation.

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --eleventh AND 0 17 --twelfth AND 0 23 --thirteenth AND 0 25 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --wire-credit --adaptive-charge --trace-budget --preloaded-trace --solver "$SOLVER"
```

Append the gate flags, `--min-guard-reads`, `--seconds`, and the new switches listed below. F = `--first-or-lines`, C = `--guard-read-ceiling`, T = `--branch-packing-tree`.

| Fixed gates 14 and 15 | h minimum | Switches | Budget | Actual verdict |
| --- | ---: | --- | ---: | --- |
| OR(14,18); AND(1,39) | 26 | F | 10 s | UNSAT on 56 rows (solver result) |
| OR(14,18); AND(1,39) | 25 | F | 10 s | UNSAT on 56 rows (solver result) |
| OR(13,19); AND(1,39) | 26 | F | 10 s | UNSAT on 56 rows (solver result) |
| OR(14,18); AND(1,39) | 24 | F | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| OR(13,19); AND(15,32) | 26 | F | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| free | 26 | F | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| free | 26 | C | 10 s | UNSAT on 56 rows (solver result) |
| OR(13,19); AND(1,39) | 25 | C | 10 s | UNSAT on 56 rows (solver result) |
| OR(13,19); AND(14,32) | 25 | C | 120 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| free | 25 | C | 120 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| OR(14,18); AND(1,39) | 24 | C | 120 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| OR(14,18); free | 25 | C+T | 10 s | UNSAT on 56 rows (solver result) |
| OR(14,18); AND(1,39) | 24 | C+T | 10 s | UNSAT on 56 rows (solver result) |
| OR(14,18); AND(1,39) | 23 | C+T | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| OR(14,18); OR(13,19) | 24 | C+T | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |

## Verification and resumption

- PlaneCase35FirstOrLines: ACCEPTED (check), 2240 rechecked constants, axioms propext, Quot.sound, Classical.choice.
- PlaneCase35GuardReadCeiling: ACCEPTED (check), 2382 rechecked constants, axioms propext, Classical.choice, Quot.sound.
- The manifest source digests and all 87 definition modules were matched against upstream, and both expanded statements were independently elaborated. Separate Lean checks instantiated the 779 ordered-by-index exclusions, the guard cap at size 63, and the 19 ORs at gate 7.
- Next general boundary: the complete 13-gate prefix with h=25. The OR(13,19), AND(14,32) continuation at h=25 is still UNKNOWN. For OR(14,18), AND(1,39), start at h=23. An independent next formalization would promote the recursive packing-tree replay and gate-15 negative families into Lean. The unrestricted 63-gate question remains open in this work.

Prepared single-file commit `99876da6fb9c9c7f85e48180338ac0debd995272` on the checked upstream base. [One-file comparison](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-guard-read-ceiling?expand=1).
