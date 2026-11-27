# L-meta-2625 — trace density in the thirteen-gate branch of case 35

Resume from `d1c7bb1498cd67794e0b839f5510f0c50007083e`. Checked upstream `b556b29a7061d89500118bb564fcb32a452400b2`, four author PRs, and 36 prepared/main/research fork branches before starting. #7762 and #8170 were merged, both with ACCEPTED checker comments and no outstanding reviews. The scoped desk returned no unit or lease. No unrestricted size-63 result was found upstream. New material is fork research.

The prefix in physical gate order is OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24), AND(15,32), AND(25,32), AND(0,17), AND(0,23), AND(0,25). Wire numbering starts at zero. Guard 32 is the result of gate 7. Let h count ANDs with 32 as a physical operand (each gate counts once). Two such reads occur in the prefix. A paid AND in this note is a suffix AND without guard 32 as a physical operand. All target checks use the same 52 positive and 468 negative rows.

## From eight paid ANDs to 24 ORs

On a family of negatives, a pair is adjacent when some positive witness has each of its initial true bits true on at least one endpoint, and a true guard bit true on both endpoints. For a separating circuit the bits read on those negatives by the paid AND probes distinguish every pair in a clique. Choose either operand as probe independently at each gate. This follows by propagating the positive-witness property gate by gate when the endpoint probes agree. Guard ANDs act as guarded copies. Coloring by some probes permits dropping those probes at a cost of the number of colors. The generic bound is formalized in `PlaneColoredTraceBudget`.

For each of the 39 starting wires the program finds 129 pairwise-adjacent negatives on which that wire is constant. A separate 129-clique has the guard false throughout. Eight probes with one constant bit could distinguish at most 128 negatives there. Therefore neither a starting wire nor a subsequent guard-AND output can supply a paid port. If two different gates read the same physical wire, orient both toward that wire, again losing a bit. An AND with two identical operands is a copy and may omit its probe entirely. Finally, if a paid output feeds a later paid gate, orient the later probe toward the output. It implies the earlier probe whichever parent was chosen, leaving at most 192 eight-bit words. The physical 218-clique excludes this. Thus the sixteen ports require sixteen distinct suffix OR outputs.

For negative j choose distinct positive flags such that each starting column false on j hits at most one flag. If a separator accepts all selected flags, then f_j flags require at least f_j−1 ORs false on j. ANDs and ORs true on j cost nothing in that accounting. `PlaneNegativeOrBudget` proves the general statement for arbitrary DAG reuse. The stored 218-clique has sum f_j = 3862. Writing R for the number of suffix ORs, the total number of true OR entries on these negatives is at most 218(R+1)−3862. Orient all probes left and then all right. Each orientation injects into the eight-bit words; the 218 lightest such words have weight 787. The sixteen distinct ORs therefore contribute at least 1574 true entries. Consequently R ≥ ceil((3862+1574)/218)−1 = 24.

The existing 19-OR and eight-paid-AND floors hold here. For a size-63 continuation at h≥25, at most 27 of the 50 suffix slots are available after charging guard reads. Nine paid ANDs plus nineteen ORs exceed that allowance; eight paid ANDs plus 24 ORs do too. Thus this entire fixed-prefix case requires h≤24. At h=24 only nine paid ANDs, nineteen ORs and twenty-two new guard ANDs fit. The 13-gate prefix is essential.

| Extra fixed gates | Clique | Sum of flag widths | Minimum OR ones from probes | OR floor with 8 paid ANDs | Excluded at size 63 |
| --- | ---: | ---: | ---: | ---: | --- |
| none | 218 | 3862 | 1574 | 24 | h≥25 |
| OR(14,18), AND(1,39) | 183 | 3146 | 779 | 21 | h≥23 |
| OR(13,19), AND(1,39) | 218 | 3729 | 1574 | 24 | h≥24 |

In the middle row two initially available wires account for at most 189 true entries. At most two ports from earlier paid outputs are possible: two distinct receivers would realize two bit implications simultaneously, permitting at most 160 words. Allow 256 true entries for those two ports. The previous packing tree supplies the separate 19-OR floor for that row; the last row uses the separate 18-OR floor.

## Preload consequences at h=24

Delete a selected paid AND and give its output value as an extra initial column. Shift references to the extra primary input or the surviving wires. This keeps the number of ORs, including ORs occurring before the selected gate. For each of the 741 unordered pairs with repetition from the 38 pre-existing non-guard wires, explicitly preload their AND and repeat the clique/packing computation. Each needs at least 24 ORs with the remaining eight paid ANDs. Thus no paid gate in the h=24 suffix can take both its operands from these 38 wires.

For an arbitrary preload V bounded by a column D, delete all positive pair witnesses hit by D and keep at most one possibly hit positive in every packing. This gives a conservative test for every V≤D regardless of its particular values. On the base instance it excludes outputs bounded by 25 of the 39 starting columns (indices in the replay script output). For support size ≤2, use D true on every negative and on only the specified positives. All 1+52+1326 = 1379 support sets gave a lower bound above 19. Hence each of the nine paid ANDs must accept at least three positives. This excludes, for example, OR(13,19), AND(14,32), OR(1,2), AND(4,41) at h=24.

## Reproduction and solver log

Run `python research/order3_case35_colored_trace.py` and `python research/order3_case35_preload_density.py` from the fork. The latter checks the preload ledger. The full sparse-support replay runs when `--sparse-density` is supplied below. Pinned solver is the CaDiCaL binary shipped with the repository-pinned Lean 4.36.0. The model starts with all 52 positives plus four negatives; a model must survive all 520 test rows. Numeric exclusions depend on the separately replayed certificates embedded as SAT cuts. In particular a solver UNSAT after adding such cuts is not an independent kernel proof of those cuts. Budgets in seconds are for the solver, excluding model and certificate construction.

Common invocation (substitute H and append the table options, then `--seconds B --solver /path/to/pinned/cadical`):

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads H --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget
```

| H | Additional options | B | Verdict |
| ---: | --- | ---: | --- |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --colored-trace` | 90 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 25 | `--preloaded-trace --guard-read-ceiling --colored-trace` | 120 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --after-fifteen OR 1 2 --after-fifteen AND 39 41` | 30 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --after-fifteen OR 1 2 --after-fifteen AND 39 41 --colored-trace` | 10 | UNSAT on 56 rows (solver result) |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --after-fifteen OR 0 3 --after-fifteen OR 0 9 --after-fifteen OR 0 13 --colored-trace` | 10 | UNSAT on 56 rows (solver result) |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --after-fifteen OR 1 2 --after-fifteen OR 4 6 --after-fifteen AND 41 42 --colored-trace` | 90 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --after-fifteen AND 0 40 --colored-trace` | 10 | UNSAT on 56 rows (solver result) |
| 25 | `--preloaded-trace --guard-read-ceiling --or-trace-density` | 10 | UNSAT on 56 rows (solver result) |
| 24 | `--preloaded-trace --guard-read-ceiling --or-trace-density` | 150 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 25 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --or-trace-density` | 10 | UNSAT on 56 rows (solver result) |
| 24 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --or-trace-density` | 120 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 23 | `--fourteenth OR 14 18 --fifteenth AND 1 39 --preloaded-trace --guard-read-ceiling --or-trace-density` | 10 | UNSAT on 56 rows (solver result) |
| 22 | `--fourteenth OR 14 18 --fifteenth AND 1 39 --preloaded-trace --guard-read-ceiling --or-trace-density` | 120 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 24 | `--fourteenth OR 13 19 --fifteenth AND 1 39 --preloaded-trace --guard-read-ceiling --or-trace-density` | 10 | UNSAT on 56 rows (solver result) |
| 23 | `--fourteenth OR 13 19 --fifteenth AND 1 39 --preloaded-trace --guard-read-ceiling --or-trace-density` | 120 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 24 | `--preloaded-trace --guard-read-ceiling --or-trace-density --preload-density` | 120 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 24 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --or-trace-density --after-fifteen OR 1 2 --after-fifteen AND 40 41 --preload-density` | 10 | UNSAT on 56 rows (solver result) |
| 24 | `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth AND 4 5 --preload-density` | 10 | UNSAT on 56 rows (solver result) |
| 24 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --or-trace-density --after-fifteen OR 1 2 --after-fifteen AND 4 41 --preload-density` | 90 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 24 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --or-trace-density --after-fifteen OR 1 2 --after-fifteen AND 4 41 --preload-density --sparse-density` | 10 | UNSAT on 56 rows (solver result) |
| 24 | `--preloaded-trace --guard-read-ceiling --or-trace-density --preload-density --sparse-density` | 150 | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 24 | `--fourteenth OR 13 19 --fifteenth AND 14 32 --preloaded-trace --guard-read-ceiling --or-trace-density --sparse-density` | 120 | UNKNOWN, 56 encoded rows, 0 decoded candidates |

## Verification and next case

- PlaneColoredTraceBudget — ACCEPTED (check), 1739 constants; axioms propext, Quot.sound, Classical.choice. [One-file comparison](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-colored-trace?expand=1).
- PlaneNegativeOrBudget — ACCEPTED (check), 1742 constants; axioms propext, Quot.sound, Classical.choice. [One-file comparison](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-negative-or-budget?expand=1).
- The manifest hashes matched all 87 upstream definition modules, and each separately expanded statement compiled against the checked module. The port classification, concrete finite replay and preload sweeps above are computational applications. No whole-branch or unrestricted 63-gate theorem is claimed as checker-accepted.
- Resume at the full 13-gate prefix with h=24 (150 s UNKNOWN), OR(14,18)/AND(1,39) with h=22 or OR(13,19)/AND(1,39) with h=23 (both 120 s UNKNOWN). The next structural target is the first paid AND after the 13-gate prefix, which must use a later wire and have at least three positive hits.
