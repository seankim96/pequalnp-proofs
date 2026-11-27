# Case 35: OR(4,8) and an independent-product bound on 21 rows

Research checkpoint for L-meta-2625, based on fork commit a6346205c5726d6629b4d439b95ffd591611d16c and upstream acbec56de1c52322de7f1031b91b31030e3495b6. The desk returned not_open and issued no lease. These results address restrictions of the 63-gate question.

## First OR exclusion

Fix the same first 17 gates as in the preceding guarded-AND-cover checkpoint, including gate 17 = AND(7,41). Work in the h=20 branch with 19 ORs, 18 physical guard ANDs and nine paid ANDs remaining. After X=OR(4,8), replay the previous second- and third-OR certificates, then the new 4-8-search bank on all 52 positive and 468 negative rows.

* Eighteen surviving ordered second/third combinations required a fourth-OR check. All 50,861 fourth values counted across these combinations were excluded by width-16 packing. Values shared by different triples are counted in each. Fourteen extra products using the third OR required individual paid-first checks. With the product supplied and none of the three ORs preloaded, two certificates require at least 21 ORs and twelve require at least 22.
* For the outstanding earlier cross at Y=OR(21,25), supply X AND Y without spending an OR. The packing requires at least 20 ORs against 19 available.
* Search used seed 3001, 40 randomized starts plus one initial choice per negative, a three-second cap per packing MILP and an eight-second per-MILP clique cap in the paid checks. The replay verifies the actual witnesses, independent of these discovery limits.
* The cumulative replay now excludes 132 of 230 first values; 98 remain. With the cuts, fixing X alone, or X followed by Y=OR(11,42), Z=OR(13,21), gave CaDiCaL UNSAT on the 56-row encoding (10-second budgets). The free suffix after gate 17 timed out at 60 seconds: UNKNOWN, zero candidates.
* Next first value is X=OR(4,10). The frontier enumerator lists 21 second continuations and 28 third continuations across them before the separate probe below. The baseline on Y=OR(13,42), Z=OR(12,14), without the cumulative first-OR cuts, timed out at 45 seconds on 56 encoded rows with zero candidates: UNKNOWN.

A subsequent width-16 search with seed 3011 (the same per-MILP caps) and an independent replay excluded all 2,792 fourth-OR values for that triple. All products with Z are dominated by earlier products or available values, and X AND Y is dominated. The standalone replay is replay_four_ten_probe(base) in the frontier module. This probe is separate from the cumulative SAT encoding and the whole-first count. Resume with X=(4,10), Y=(13,42), Z=(11,14).

To replay, run the commands in the parent report, using the updated --shared-first-ors cut bank. The new frontier is printed by python research/order3_case35_or_frontier.py 4 10. To target a candidate, append --after-fifteen OR a b for each additional gate after the fixed prefix.

## Eleven independent products

Use positive indices 4, 8, 14, 18, 23, 27, 28, 32, 42, 46, 51 and negative indices 49, 76, 200, 254, 298, 321, 361, 374, 435, 453, separately zero-based in test_rows() order. At the 43-wire pool, each OR operand may use any of the 43 raw sources and their 43 copies masked by physical guard wire 32. Allow arbitrary free terms in the output OR. Each independent paid term is the AND of two such ORs. A masked output product can absorb the mask into one operand.

Every source that hits a pivot hits a chosen negative. For every pair of distinct pivots there are three of the ten negatives such that a side true on both pivots hits at least two of those three. Consequently two sides true on both pivots intersect on a negative. Each safe product covers at most one pivot, and selecting a product for each pivot gives an injection into the set of paid products. Thus at least eleven are necessary even on these 21 rows. The 10-second negative-set minimization run supplied a feasible set; its minimality is unknown. All 55 majority triples are independently replayed. The theorem's raw_bound declaration computes the actual prefix signatures from concrete 26-bit rows. The named main theorem exposes the same inequality on the explicitly computed signatures.

## When paid gates may depend on one another

Use the identical 21 rows, allow arbitrary ORs and guard masks between paid ANDs, and drop physical OR and guard-read budgets. An exact CNF lets a single selector choose each source for an operand on all 21 rows. Each later side and the final OR may also select any earlier paid output, masked or direct. Duplicate initial signatures are collapsed only on these 21 rows. Unused paid gates may be padded, so UNSAT at k excludes any smaller budget.

| Paid AND budget | CaDiCaL outcome on the 21-row core | Solver limit |
| --- | --- | --- |
| 2 | UNSAT | 12 s |
| 3 | UNSAT | 12 s |
| 4 | UNSAT | 12 s |
| 5 | UNKNOWN | 12 s and 180 s |
| 6 | SAT | 12 s |

A second run at five with commutative operands in lexicographic order and redundant masked selectors removed also timed out at 120 s (UNKNOWN). An experimental encoding tracking negative upper bounds returned UNSAT at four, SAT at six and UNKNOWN at five (120 s). A separate 90-second stochastic search (seed 3011) reached ten of the eleven positive pivots at five paid gates with no negative errors on the core. It produced no feasible five-gate witness and gives no lower bound.

The decoded six-product model is saved in case35-21rows-six-dependent.json. Source indices 0–42 name initial wires, 43–85 are their guard-masked copies, and each new product appends its output followed by its masked copy. The six-product model is replayed on all 520 rows. It accepts all 11 selected positives and rejects all ten selected negatives; it accepts 13/52 positives and **372/468 negatives** on the full table. The dependent paid optimum on the core lies between five and six by the solver results. A separate exact enumeration of conjunctions of OR clauses on the same 21 rows gives eight clauses (seven binary ANDs), with witness output accepting 16 positives and 366 negatives on the full table. These small-core witnesses do not satisfy the project specification.

Run from the repository root:

```sh
python research/order3_case35_twenty_one_rows.py
python research/order3_case35_dependent_core.py /path/to/pinned/cadical 4 12
python research/order3_case35_dependent_core.py /path/to/pinned/cadical 5 180
python research/order3_case35_dependent_core.py /path/to/pinned/cadical 6 12
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneElevenSeparatedProducts.lean research/statements/PlaneElevenSeparatedProducts.txt check
```

## Verification and desk

Pinned Lean 4.36.0 and the upstream checker returned **ACCEPTED (check)** for PEqualNP.Research.PlaneElevenSeparatedProducts against the explicit-signature statement. The verifier rechecked 1,736 constants, with only propext, Quot.sound and Classical.choice. All 87 definition-source digests matched acbec56de1; a separate Lean import compiled the exact statement. We also separately compiled the raw_bound declaration against the statement that recomputes all 17 prefix gates on the raw test inputs. An earlier checker invocation for the raw statement ended with exit 137 and gave no verdict. The published file contains both declarations.

The one-file contribution is fork commit 1d2f60d4f837bfab0a011fdbba4831a8c0c31db6 on research/l-meta-2625-eleven-separated-products. Upstream a1bfa5ad9f was checked for relevant changes after validation: no change to the project definitions, toolchain, checker or R_meta_2625 files. The desk did not assign this gap or issue a lease, so no project submission, renewal or release was made. Upstream PRs #7762 and #8170 were merged with ACCEPTED checks and no requested revisions.
