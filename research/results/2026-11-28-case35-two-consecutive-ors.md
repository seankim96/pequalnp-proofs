# L-meta-2625 — Two consecutive non-guard ORs at the exceptional h=19 prefix

Research parent 14195c735ac0e1bd190ca14ff333e225c49e051e. On 2026-11-28, upstream b8b12a2eef984b0fb99cf6ea3ce84a1cb660cdd2 still contained R_meta_2625_50, _317, and _487 and no L_meta_2625 proof. The desk returned no lease for this unit. No other lease was touched. Both #7762 and #8170 were merged and had no outstanding review threads.

## Fixed prefix

Use the parent checkpoint's case 35 prefix of 17 gates, then OR(14,18) at wire 43 and AND(1,43) at wire 44. Fix exactly 19 physical ANDs reading guard wire 32, with nine ordinary ANDs and twenty ORs after gate 17, in a 63-gate circuit. After wire 44 the budgets are eight ordinary ANDs and nineteen ORs. The parent excludes an ordinary AND before the next OR and leaves 1,212 possible first OR values. Guard reads can occur between the named operations.

**New numerical verdict.** For every one of those 1,212 possibilities the next non-guard operation after that OR must also be an OR. Equivalently, the suffix after wire 44 must start with at least two non-guard ORs. This is a certificate exclusion for a fixed prefix and operator budget. It makes no assertion about the other h=19 split or other prefixes.

Let Y be the first new OR output on the 52 positive and 468 negative rows. Any subsequent operand before another OR is an original wire, Y, or a guard-masked copy of one of these. If the next ordinary AND uses only old wires, its unmasked product was handled at the parent checkpoint. Otherwise its output is P or P AND guard, for P = Y AND v with v an original wire or Y. The verifier reconstructs 24,574 distinct P. If an older rejected product U dominates P (it accepts at least P's positive rows and at most P's negative rows), preloading U lets a separating circuit bypass this AND. Y may still be computed in its original place and charged the original OR. Masking the replacement when necessary preserves dominance and consumes no ordinary AND or OR. The relaxed circuit has at most seven ordinary ANDs, nineteen ORs, and arbitrarily many guard masks. Hence the old exclusion applies even if a reconstructed Y costs an OR.

Exactly 2,019 products needed new certificates. In 1,717 cases 129 pairwise incompatible negatives exceed the 128 signatures of seven probes. In the other 302 cases every starting wire is constant on a certified 65-clique and the guard is false on another 65-clique. The parent seven-probe argument then charges fourteen distinct OR operands. Summing true and false OR entries on the packing clique gives floors of 22 ORs in 11 cases and 23 ORs in 291 cases. All exceed the relaxed budget of 19. Replay checks each clique edge, all flag packings, the budget arithmetic, and coverage. The compressed ledger shares repeated integer lists across records.

For OR(4,44), the broader h ≥ 19 CaDiCaL query fixed the first 20 physical gates and allowed either suffix operator split. With a 45-second solver budget it returned UNKNOWN on 56 encoded rows, with zero decoded candidates. The exact-budget exclusion above uses all 520 rows. The 129-clique search is greedy and has no solver timeout. Seven-probe discovery used SciPy/HiGHS with two seconds per row packing and five seconds per clique objective. All reported exclusions have replayable integer witnesses.

## Lean lemma

PlaneDeleteCopy removes a unary OR copying an existing earlier wire. For any fixed input width n, a single replacement circuit computes the same output on **every** length-n row and has exactly one fewer gate. It preserves Monotone2 when the original circuit is monotone with fan-in at most two. The proof redirects every read of the removed slot to the copied source, decrements later indices, and also remaps the output. It handles direct output from the removed slot, fan-out to multiple later gates and out-of-range reads. Together with the previous PlaneAbsorbedAnd result this allows actual size reduction when a negative-row-absorbed AND has an earlier source wire at the fixed width.

## Reproduction

From the repository root:

```sh
python research/order3_case35_h19_two_consecutive_ors.py
python research/order3_case35_h19_or4_44.py
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneDeleteCopy.lean research/statements/PlaneDeleteCopy.txt check
```

The one-file Lean contribution is 4ed795e872cbeb1f1e262c4afd94fef02a2def12 on research/l-meta-2625-delete-copy. The repository's Lean 4.36.0 checker accepted the theorem, rechecking 1,735 constants. The manifest's 87 project definition hashes match upstream, and its proof hash matches the file on the fork. A separately elaborated example checked the exact recorded type. The reported axioms are propext, Classical.choice and Quot.sound.

## When the first OR is OR(4,44)

Set Y = OR(4,44) (wire 45). The next non-guard gate must be another OR. In the extended pool with Y there are 2,725 possible second OR values Z, including unions of guard-masked sources. The 1,444 exclusions from the parent apply at this slot: if their value is dominated by a free source then its OR can be deleted, and if a stronger preloaded value has a verified eight-AND floor of 19, then the remaining 18 ORs cannot implement the circuit. Y can still be computed normally in either argument. This leaves 1,281 values before new OR-floor tests.

If the following non-guard operation were an ordinary AND, a product not involving Z could have been provided early by the two-OR result above. Otherwise its unmasked value is Z AND u with u an original wire, Y, or Z. Both Y and Z can be recomputed at their original cost after supplying that product. Above the already certified preloads, precisely 89 extra products are needed in the 1,281-value superset. Sixty-two have 129-cliques and the other twenty-seven have OR floor 23 with seven probes. Thus for this choice of Y **three** non-guard ORs must occur before the next ordinary AND. Run `python research/order3_case35_h19_or4_44_third_product.py` for the full replay.

The separate second-OR sweep prepays both Y and Z. The residual budget is eight ordinary ANDs and seventeen ORs. It tested all 148 union values using Y or its guard mask as an operand, and then the other 1,208 previously unexcluded independent union values. The sets overlap the parent's prior exclusions, so these discovery counts are not additive exclusion counts. Each eight-probe clique MILP had eight seconds and the per-negative 52-flag packing MILPs had no separate timeout. For the three dependent values left by the first pass (Y OR 8, Y OR 11, Y OR 12), four more clique objectives and up to five clique sizes per objective yielded no stronger certificate.

**Second-OR verdict.** The unpruned sweep produced 1,303 strict floor certificates. Direct dominance and the inherited exclusions left 53 second values. For each of these, eliminate a source if a different currently available source (possibly masked by the guard) has at least its positive ones and no additional negative ones. Leave the guard in place. A separator can replace all uses of the eliminated source by the dominating signal and at most a free guard AND. This argument composes one deletion at a time. Fill vacated positions with the false column to retain the guard index. The resulting relaxed-instance floor reached 18 for 27 additional values. A four-objective refinement on the remaining 26 found no stronger certificate. In total, **2,699 of 2,725 second values are excluded and 26 remain**. All 1,330 stored eight-AND certificates give OR floor 18. Each strict comparison here is against the residual OR budget 17.

**Third-OR follow-up.** Among the 26 second values, choose Z = Y OR i for i in {8,11,12}. All three branches require a third non-guard OR. Each has 2,865 possible third-OR values before exclusions. The previous prepayment and replacement certificates still apply if the covered OR value is produced in a later slot; previously fixed intervening gates remain charged to the original budget. This reduces each third-OR search to 166 possible values. Free Y, Z, and the candidate third value, prune the dominated inputs as above, and check whether eight ordinary ANDs can finish with sixteen ORs. All 441 strict certificates have floor 17. The same eight-second clique limits and uncapped per-row packing MILPs apply. The replay optionally tests whether a certified pair of supplied columns also dominates both required columns of a different branch.

| Second OR value | Additional third-OR certificates | Unexcluded third OR values |
|---|---:|---:|
| Y OR 8 | 149 | 17 |
| Y OR 11 | 147 | 19 |
| Y OR 12 | 145 | 21 |

Run `python research/order3_case35_h19_or4_44_third_or.py` to regenerate those exact remaining sets. For all three, OR(5,10) is one concrete remaining third value. A next target is the fixed ordinary sequence Y = OR(4,44), Z = OR(8,45), T = OR(5,10). Determine whether the next ordinary AND can use T after paying those ORs, or exclude one of the 17 pending choices. The separate operator split and the unrestricted 63-gate instance remain unresolved. The latest upstream recheck at 1931b3cb024bd2d5d11db0463d90f9e8e3405d3d still has the same three reductions and manifest definition hashes.
