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






## Ordering of the first paid AND at h=24

The first paid AND requires **at least three suffix OR gates before it**, even if arbitrarily many guard ANDs are interspersed. This only concerns the size-63, thirteen-gate prefix at h=24. It puts the earliest possible first paid AND at gate 17. It also excludes every enumerated output signature for any of the nine paid gates, independently of its position.

Let B be the 39 starting columns together with their masks by the guard. It has 66 distinct signatures on the 520 rows and is closed under masking. Let U2 and U3 be unions of at most two or three B terms (repetition allowed). They have 2,032 and 39,270 signatures. Each U3 value can replace a paid gate at the cost of at most two extra ORs and any number of guard ANDs. The resulting eight-paid circuit would have at most 21 ORs, below its certified floor of 24. The unrestricted number of guard ANDs is important in this replacement argument.

Before the first paid AND, all intervening AND gates simply mask by the guard. With two independent ORs, either operand of a following paid gate lies in U2. If the second OR depends on the first, write the first result as u. After distributing masks the second is a union of at most three B terms. Its product with a B term lies in B∩U3 (here ∩ denotes taking the bitwise product of one term from each family). Its product with a masked or unmasked u either simplifies by absorption or has the form u∩(guard∪b), with b in B. The latter is in U2∩U2, and a final mask is distributed onto either operand. If both operands descend from the second OR, their product is that OR or its masked copy, already in U3. These alternatives also cover zero or one OR by repetition. This bounds the complete grammar, including reused physical wires.

For one OR alone, the 66 masked initial signatures give 721 no-OR products and 30,462 one-OR candidates after removing immediate copies; 98 residual signatures each need at least 24 ORs after exact preloading. For two ORs, remove U3, signatures with at most two positive bits, and signatures covered by a certified dominating column. The U2×U2 products leave 28,072 candidates and the B×U3 products leave 2,335. Their union has 30,317 distinct signatures in 2,447 positive support classes. The interval replay groups equal positive masks, combining the bitwise intersection and union of each block as lower and upper bounds for its hypothetical preloaded input. A positive witness may keep a newly introduced true bit whenever either negative is forced true; otherwise it must avoid the upper mask. The same lower envelope identifies packings needing no thinning. If a block does not close, split it and eventually check a singleton. Exactly 30,312 signatures were excluded this way in 2,451 interval evaluations.

Five exceptional values each accept three positives and no negatives. For a 161–192 clique, a probe selected from an earlier paid AND implies a distinct earlier bit, making that probe true on at most 64 codewords. Two receivers cannot both use paid-output probes, because the two implications would permit at most 160 codes. In each orientation use the smaller of the unrestricted minimum weight and the minimum weight among words obeying one implication minus 64. For a guard-false clique of size m>64, guard-AND inputs likewise can occur at just one receiver. If m≤128 and such an input occurs, a probe at any other gate must hit between m−64 and 64 of that clique: pinning the guard probe at zero leaves at most 64 different codes for each value of another bit. Bound the cost of all balanced raw wires plus the largest exceptions fitting in the remaining ports of that receiver. Check all possibilities of zero, one and two guard-AND ports. Every finite pair witness and flag packing in the five explicit certificates is rechecked.

| Positive row IDs (zero-based) | Negative hits | Clique size | Certified OR floor after preloading |
| --- | ---: | ---: | ---: |
| 9, 12, 28 | 0 | 173 | 21 |
| 10, 18, 36 | 0 | 175 | 21 |
| 27, 34, 37 | 0 | 167 | 20 |
| 19, 26, 45 | 0 | 174 | 21 |
| 39, 47, 51 | 0 | 175 | 21 |

These floors all exceed the 19 ORs in a candidate h=24 continuation. Reproduce with `python research/order3_case35_two_or_preloads.py`. Only integer checks on stored certificates are required at replay time. The optimization routine that proposed the exceptional families is outside the trusted calculation.

`PlaneOneOrGuardClosure` formalizes the physical one-OR normal form for any number of guard ANDs before and after it. ACCEPTED (check), 1,735 rechecked constants, axioms propext, Quot.sound, Classical.choice. The exact expanded type compiled and the manifest matched all 87 definition modules on the upstream commit. [One-file comparison](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-one-or-closure?expand=1). The two-OR classification and the resulting h=24 exclusion are finite computational reductions.

Additional runs use the common invocation above, with H=24.

| Additional options | Budget | Verdict |
| --- | ---: | --- |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 0 3 --fifteenth AND 27 39 --sparse-density` | 60 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 0 3 --fifteenth AND 27 39 --first-paid-order` | 10 s | UNSAT on 56 rows (solver result) |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --first-paid-order` | 150 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 0 3 --fifteenth OR 4 6 --after-fifteen AND 39 40 --first-paid-order` | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 0 3 --fifteenth OR 4 6 --after-fifteen AND 39 40 --three-before-paid` | 10 s | UNSAT on 56 rows (solver result) |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 19 21 --fifteenth OR 22 39 --after-fifteen AND 9 40 --three-before-paid` | 10 s | UNSAT on 56 rows (solver result) |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --three-before-paid` | 150 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| `--preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41 --three-before-paid` | 120 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |

Next open frontier: the 13-gate h=24 prefix with at least three suffix ORs before the first paid AND, positive support at least three for each paid gate, and the 25 dominating-column exclusions. A concrete surviving test is OR(17,19), OR(20,24), OR(39,40), AND(7,41): it computes the four flags at point 7 and was UNKNOWN in 120 solver seconds. Assess this specific preload or vary the third OR.

### Verification limit for the concrete combined file

A case-specific Lean file in `research/drafts/PlaneCase35ProbeDensity.lean` compiles with the pinned toolchain and its expanded statement compiles independently. It includes the physical 39 columns, 218 negative rows, the 3,862-flag incidence count, and the conditional 24-OR theorem under two supplied injective eight-bit orientations at sixteen distinct OR ports. The repository checker built this file, but the verifier exited 137 on both runs. Its checker verdict is **CHECKER FAULT**, with no ACCEPTED verdict. The raw port-classification and first-paid exclusions remain finite replays. The draft and its exact statement are retained so the next run can reduce the kernel replay cost. To reproduce, copy the draft to `lean/PEqualNP/Research/PlaneCase35ProbeDensity.lean` on the checked upstream commit and run the repository checker on it with the adjacent statement.
