# L-meta-2625 · Nine further ordinary ANDs after the seven-gate case-35 prefix

Parent research checkpoint 726d071c7ace48889d6dc8e64d348090782765b1. Upstream snapshot 2e917d660590be18b2e9c011fb60e5ad06f2c20e. The unrestricted size-63 monotone circuit question is unresolved in the inspected upstream tree.

## A lower bound for physical suffixes

The first seven gates, in order, are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6). Inputs are wires 0–25. The seventh gate creates guard wire 32. The theorem quantifies over a list of physical two-input monotone gates, with stable wire indices and fresh outputs numbered from 33, and over any output index. If the circuit accepts the 52 selected positives and rejects the 264 selected negatives, its suffix contains at least nine AND gates whose two inputs both differ from wire 32. Four such ANDs already occur in the prefix, so the entire circuit requires at least thirteen of them. The theorem allows any number of ORs, any number of ANDs reading the guard and arbitrary sharing. It gives a conditional lower bound after seven fixed gates. Whether any unrestricted circuit of size 63 exists remains open.

The first 264 negatives in the depth-seven packing in case35-clause-covers.json.gz suffice. For each pair of different negatives a six-bit entry identifies a positive signature contained in the union of the two negative signatures. A positive-correct OR clause therefore cannot reject both. Rejecting all 264 needs at least 264 clauses. The expansion of k paid ANDs has 2^k clauses, including with free OR and guard masking. Since 2^8 = 256, k ≥ 9. The physical-to-normalized compiler in the proof handles ordinary wire indices, shared intermediate values, guard ANDs on either input, and any output selection. Its two inductive lemmas preserve evaluation and exactly count charged AND gates.

The pair table checks all 34,716 unordered pairs (69,432 ordered pairs off the diagonal). Each stored witness word holds up to ten six-bit positive indices. All numerals are at most twenty digits. The finite computations use Lean kernel decidability. The file imports only Mathlib. The formal theorem uses 52 and 264 explicit raw input masks. The test selection is reproducible from the depth-seven ledger. The bridge from an arbitrary upstream Circuit term to this indexed gate-list representation is a separate remaining step. After namespace substitution to a temporary test module, the local submission format preflight also accepted the candidate syntax. The project-pinned Lean 4.36.0 checker returned ACCEPTED against the recorded research statement. It rechecked 2108 constants. The reported axioms were propext, Classical.choice and Quot.sound. An independent Lean import checked the exact statement. The checked source digest and all 87 public definition digests were compared with the proof source and the inspected upstream snapshot.

## Fixed 17-gate physical search

These searches use the previous case-35 point-seven prefix and h=20. After its 17 gates, the remaining budget contains 19 ORs, 18 guard ANDs and nine other ANDs. X, Y and Z denote successive OR columns before the next paid gate. Search certificates are replayed on 52 positive and 468 negative rows by the cumulative verifier. Direct and cut-assisted CaDiCaL queries encode 56 rows, with the pinned distribution's solver. A timeout always counts as UNKNOWN.

| X | Second columns | Ordered triples | Fourth columns | Explicit third-OR products | Explicit two-OR crosses | Seed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| (14,25) | 21 | 12 | 33890 | 16 | 0 | 3601 |
| (21,22) | 23 | 2 | 5647 | 6 | 0 | 3602 |
| (5,10) | 22 | 24 | 67820 | 24 | 1 | 3603 |
| (5,22) | 21 | 26 | 73441 | 22 | 0 | 3604 |
| (18,21) | 20 | 6 | 16943 | 6 | 0 | 3605 |
| (12,14) | 21 | 8 | 22616 | 0 | 1 | 3606 |
| (4,11) | 20 | 10 | 28247 | 6 | 1 | 3607 |
| (4,25) | 27 | 14 | 39511 | 14 | 0 | 3608 |
| (5,16) | 23 | 0 | 0 | 0 | 0 | 3609 |
| (14,21) | 23 | 22 | 62165 | 20 | 0 | 3610 |
| (8,22) | 25 | 4 | 11306 | 4 | 2 | 3611 |
| (10,25) | 22 | 14 | 39537 | 24 | 0 | 3612 |

The 12 new first-OR values comprise 268 second-column cases, 142 third-OR continuations and 401,123 fourth-column exclusions counted per order. The ledgers include 142 explicit paid-product certificates and 5 exceptional two-OR crosses. The cumulative frontier is **173 excluded / 57 unexcluded**, previously 161 / 69 from the fixed pool of 230. An unexcluded candidate need not have a satisfying circuit.

For the previous UNKNOWN continuation (14,25)/(13,42)/(16,18), the integer replay checks all 2,791 fourth values. Charging the product of its third OR and wire 6 requires at least 22 ORs, above the available 19. The intermediate case (4,11)/(13,42)/(5,21) also returned UNKNOWN, 56 encoded rows, 0 decoded candidates in a direct 45-second run before its ledger was applied. Subsequent cut-assisted verdicts use the certified first-OR exclusions.

MILP discovery used up to three seconds per width-16 packing, one deterministic objective and up to 40 randomized objectives per negative. Clique MILPs used up to eight seconds. Auxiliary 52-variable packing MILPs for paid products had no explicit call timeout. Only concrete integer witnesses survived replay. Fixed SAT checks used ten seconds, the free-suffix check sixty seconds, and the direct next-triple baseline forty-five seconds.

| Fixed ORs in order | Cut-assisted SAT budget | Verdict on 56 encoded rows |
| --- | ---: | --- |
| (14,25) | 10 seconds | UNSAT |
| (14,25), (13,42), (16,18) | 10 seconds | UNSAT |
| (4,11) | 10 seconds | UNSAT |
| (4,11), (13,42), (5,21) | 10 seconds | UNSAT |
| Free suffix after the 17-gate prefix | 60 seconds | UNKNOWN on both runs, zero candidates decoded |

The direct 45-second run for (11,22)/(15,42)/(5,13) returned UNKNOWN. A separate seed-3613 width-16 certificate excludes all 2,790 fourth columns for this order. A second run of the repository discovery CLI reproduced the identical integer certificate. The integer verifier also checks that the two-OR cross and every product involving the third OR are dominated. This closes the named triple only. Its first column (11,22) is among the 57 unexcluded. To use this when resuming, skip exactly this triple or import its saved tests and witnesses into the first-column ledger.

Continue with X=(11,22), Y=(7,15), Z=(5,13). Its direct 45-second run returned UNKNOWN on the 56 encoded rows, with zero decoded candidates.

Reproduce from the research checkout with the pinned environment.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneSevenGatePaidLowerBound.lean research/statements/PlaneSevenGatePaidLowerBound.txt check
python research/order3_case35_or_frontier.py 11 22
python research/order3_case35_or_packing_search.py --union 11 22 --union 15 42 --union 5 13 --seed 3613 --samples 40 --out /tmp/case35-3613.json
PYTHONPATH=research python -c "from order3_case35_or_frontier import _replay_dominated_triple, columns, PREFIX13, POINT7, test_rows; print(_replay_dominated_triple(tuple(columns(PREFIX13+POINT7, test_rows())), (11,22), (15,42), (5,13)))"
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads 20  --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget  --preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41 --star-probes --after-fifteen OR 11 22 --after-fifteen OR 7 15 --after-fifteen OR 5 13 --seconds 45 --solver "$(lean --print-prefix)/bin/cadical"
```

The desk returned not_open for L-meta-2625, with no lease issued to this run. The three upstream reductions remain present, with no direct unrestricted theorem found. A second upstream check at 5245ce9b3b1f1262390339d02ec9b87801b579bf found the same three reductions, and the checker, toolchain, build configuration and checked definitions had the same bytes. PRs #7762 and #8170 are merged with accepted checks and no outstanding review requests. No new upstream PR was filed. The one-file proof is at commit cd926645213d119836e1341badc84dfe796f068c in the fork. The numerical ledgers and their manifest were published first at 42031966011a325bbad05b3afd71e3e4e5812f59 and all 13 downloaded blobs matched their local Git hashes.
