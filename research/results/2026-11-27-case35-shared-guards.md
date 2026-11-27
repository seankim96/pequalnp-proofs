# L-meta-2625 — case 35, four prefix gates and a shared OR

Parent research checkpoint: 30c7bf6d0cf6c31543d0dba0d0c3721065340d82. Upstream checkout and checker: 7f4d3f02215926e7d931d23c01d1fab581a93457, Lean 4.36.0. The desk returned `not_open` for the named unit, a state that can also mean withdrawn. No lease was issued. No unrestricted verdict was found in the public upstream tree. The published files there for this unit are reductions 50, 317 and 487. The four account PRs are closed. PRs 7762 and 8170 are merged with accepted checker comments and no outstanding requested changes.

All wire and test indices start at zero. Gates 1–6 are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27). The four-chain results also cover exchanging gates 5 and 6. After six gates there are 32 available signals. The task is to accept the 52 incident flags and reject the 468 negative tests.

## Four-gate prefix

Represent each signal as a disjunction of conjunctions of the 32 baseline signals. Remove products subsumed by another product from the same disjunction. When the products of size greater than one across the entire starting pool can be partitioned into four or fewer chains under set inclusion, a separating suffix must contain at least nine ANDs. The finite kernel certificate allows up to four exceptional positive flags.

The semantic bridge proves that normalization preserves evaluation throughout an arbitrary prefix, including gates that read earlier gate outputs. It also gives a hypothesis-free corollary for any prefix of up to four ANDs. Each such gate adds at most one product, hence four singleton chains suffice regardless of its operands, dependencies or the order of gates 5 and 6. Replaying the previous exhaustive formal wiring census gave 9,120 four-chain shapes and 96 remaining shapes out of 9,216. This census is a Python calculation. For any concrete prefix the chain hypothesis can be checked directly with `order3_chain_cover.prefix_chains`.

## Guarded outputs

A guard is the OR of two baseline signals. The circuit may apply a guard to an ordinary gate's output, intersecting with it at no charged AND cost. The guard can change from gate to gate and can be reused. For the menu of 17 guards in the source, the certificate keeps 260 of the negative rows. For every pair among them, it supplies a positive flag whose active baseline signals transfer to the union of the two rows. Additionally every guard active on the witness must be active on **both** negative endpoints. This second condition allows the induction to pass a masked output through any selected sequence of gates. With eight charged ANDs there are only 256 binary transcripts available to distinguish 260 negatives.

`python research/order3_case35_shared_guards.py` also checks all 528 possible single guards independently using a 48-bit witness mask for each negative pair. With one fixed guard the minimum retained size was 261 and the maximum was 372. With the 17 guards simultaneously it exactly reproduces the Lean removal mask and checks all 33,670 retained pairs. The single-guard sweep is numerical; the one joint menu is the scope of the Lean certificate.

## An ordinary gate-count consequence

Fix gate 7 to any OR from the same menu. Its output is wire 32. For an ordinary binary suffix let h count the AND gates reading wire 32 as either operand (count each gate only once). The resulting size inequality is **34 + h ≤ total gate count**. To see the charged AND count, translate each of these h intersections with the guard into a masked OR(x,x); all wire values stay exactly the same. There are at least nine remaining ordinary ANDs. Independently at least 19 OR gates are needed after gate four, of which gate seven is the first. The proof works with arbitrary placement, fan-out and choice of the other operand. In particular h ≥ 30 rules out every 63-gate circuit under these hypotheses. No restriction follows here for general case-35 circuits whose seventh gate or reuse count is different.

## Bounded SAT attempts

All three searches use the six gates above, order 63, and 53 free suffix gates. The first CNF contains all 52 positives and negatives 0, 1, 2 and 234. CaDiCaL comes from the pinned Lean distribution. An eventual witness has to pass all 520 tests.

| Gates 7–10 | Suffix AND / OR minima | Variables / clauses | CEGIS budget | Observed outcome |
| --- | --- | --- | --- | --- |
| AND(2,15), AND(5,15), AND(11,15), AND(4,16) | 9 / 19 | 17,013 / 543,202 | 120 s | UNKNOWN; 56 rows, 0 decoded candidates |
| OR(2,26), AND(14,32), AND(15,32), AND(25,32) | 9 / 18 | 16,960 / 543,096 | 120 s | UNKNOWN; 56 rows, 0 decoded candidates |
| Same OR(2,26) prefix, with nine ANDs that do not read wire 32 | 9 charged / 18 OR | 17,490 / 544,157 | 180 s | UNKNOWN; 56 rows, 0 decoded candidates |

The second wiring is a K(2,3) example with five exceptional flags (mask 0x3000000000130). Its ninth remaining AND follows from the shared-guard certificate even though the generic four-chain condition does not cover this wiring. Reproduce with `order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27`, the four indicated `--seventh` through `--tenth` arguments, and `--all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --seconds 120 --solver PATH_TO_PINNED_CADICAL`. Add `--shared-guard-budget` and replace 120 with 180 to reproduce the third run. A charged witness in that encoding requires the AND operator and excludes both selectors for wire 32. Every physical circuit satisfying the proved bound can choose one selector per operand.


## A sharp limitation of the pair-witness method

For OR(2,23), omit the first four flags as usual and additionally forbid flag 10. Require each remaining witness to transfer every active baseline wire to at least one endpoint, and its active guard to both endpoints. The largest possible compatible negative family has exactly **244** elements under these conditions. The primal certificate lists 244 compatible rows. The dual certificate partitions all 468 rows into 244 classes such that no two distinct members of any class can share an admissible witness. An injective transcript proof needing 257 rows cannot work with these precise hypotheses. This count gives no circuit size or SAT verdict.

Discovery used two SciPy/HiGHS integer programs (90 s cap each, both optimal) from the 276 maximal cliques of the incompatibility graph, largest clique size five. The replay verifies both certificates directly using only NumPy, independent of the optimizer. In the broader sweep of 528 single guards × 48 single omissions, the greedy search reached 257 in 23,525 of 25,344 trials. Its smallest and largest constructed families had 241 and 366 rows. The 1,819 below threshold are algorithm outcomes, not 1,819 impossibility proofs.

## Remaining work

The unrestricted 63-gate question has no verdict from this session. The numerical 792 five-flag masks include instances of K(2,2) with a separate product. A next target is a checked witness family simultaneously permitting a shared guard and one extra exceptional flag, or a checked uniform certificate for all 528 single guards. For the 1,819 numerically short families, distinguish true obstructions from poor greedy choices by certifying compatible sets or clique partitions as above. Avoid repeating the recorded CNFs with the same budget and seeds.

One-flag numerical follow-up: with just OR(2,26), dropping any one more positive among flags 4–51 still gave between 304 and 316 retained negatives. A greedy partition of those flags yielded 12 omission blocks with 257–291 retained rows per block; the replay emits their exact masks. With all 17 guards simultaneously, the same one-flag deletion heuristic found only 244–256 rows. These are constructive clique sizes, not upper bounds on what a different search might find.

## Official checker results

Each theorem was checked as a standalone file against its expanded research statement, using the pinned upstream checkout. All five manifests list only their own research module and the shared definitions. The 87 definition digests in each manifest matched upstream, and the fully expanded statement also compiled independently. The reported axioms were propext, Quot.sound and Classical.choice.

| Theorem | Official check | Kernel constants | Verified fork branch |
| --- | --- | ---: | --- |
| PlaneCase35FourChainSuffix | ACCEPTED | 2483 | [one-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/7f4d3f02215926e7d931d23c01d1fab581a93457...4553f3ade59730db69f9e2d1145b56f91dbe56a4) |
| PlaneCase35FourthGateFamilies | ACCEPTED | 2533 | [one-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/7f4d3f02215926e7d931d23c01d1fab581a93457...215d65c03d503e3d0fd3fcdc9437cd167dd8b2f1) |
| PlaneCase35SharedGuardBudget | ACCEPTED | 2048 | [one-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/7f4d3f02215926e7d931d23c01d1fab581a93457...acc7a1184f404cf063204785ae5219e94e278df3) |
| PlaneCase35SharedGuardSize | ACCEPTED | 2207 | [one-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/7f4d3f02215926e7d931d23c01d1fab581a93457...fdb6aa18c0062eb4cde08cd5a607728afcab3503) |
| PlaneCase35GuardOmissionMaximum | ACCEPTED | 2233 | [one-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/7f4d3f02215926e7d931d23c01d1fab581a93457...ee284a58e79f17839f8363777327898bba4cf417) |

