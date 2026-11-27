# L-meta-2625: exact clause covers and the first paid AND

Based on research checkpoint 58f557b4fda487a2d22329a1021017e3e9825153 and upstream 5023774ccd8b6128922482ba9c6d2ba176eb3738. Use the same 52 positive and 468 negative test rows. All prefix lengths below refer to initial segments of the case-35 17-gate prefix in the parent. Guard masking uses wire 32. A paid AND is an AND other than the free guard masks.

## Formal result

PlaneGuardedClauseExpansion proves that a suffix with k paid ANDs, arbitrary ORs and arbitrary applications of a single guard has a representation by a conjunction of 2^k OR clauses over the initial raw or masked sources. Clauses may repeat. Each paid gate takes the AND of two OR operands and appends its result to the available wires. The gate may reuse any earlier product. Each OR operand and the output may select raw or guard-masked signals. Successive ORs flatten and a mask distributes over OR, so this representation allows unbounded OR and mask stages.

For the induction, substitute each of the two operands for the first paid output in every clause for the remaining gates. Mask bits combine by OR under substitution. For a fixed row, every clause is monotone in the new bit, so evaluating at the meet of the two operand bits is exactly the AND of the two evaluations. This doubles the number of clauses. The result holds for every initial Boolean valuation and either guard value.

The pinned Lean 4.36.0 project checker returned **ACCEPTED (check)**, replaying 1,731 constants. The exact recorded statement compiled independently and all 87 definition digests matched the checked upstream snapshot. The one-file proof commit is eddafc702c50e1c86a8b8051e450d37c9435acca.

## Exact finite optima

A clause must intersect the source signature of every positive. For the upper certificate, intersect the truth columns of the saved clauses and compare to the exact target. For the lower certificate, take a saved family of negative rows. For every distinct pair, the union of their signatures contains a positive signature. Hence every clause rejecting both rejects a required positive, and each correct clause can reject at most one member of the family. Matching certificate sizes give the exact minimum independently of any optimization status.

| Prefix length | Minimum clauses on all 520 rows | Further paid ANDs required by expansion |
| --- | ---: | ---: |
| 7 | 275 | 9 |
| 8, 9, 10 | 257 | 9 |
| 11 | 251 | 8 |
| 12 | 236 | 8 |
| 13, 14, 15, 16 | 218 | 8 |
| 17 | 160 | 8 |

At length 17, 38 positive rows suffice to witness all 12,720 pair obstructions among 160 selected negatives. The same 160-clause optimum therefore holds on this 198-row core. The numerical certificates are replayed by Python. The Lean theorem establishes the general expansion.

## One paid product after 17 prefix gates

With no preceding OR, direct products of the 73 distinct raw/masked sources yield 840 distinct columns. For **each** value the replay matches lower and upper certificates. The residual optimum ranges from 142 to 160. In 785 cases it remains 160. Counts by residual size are printed by the replay.

Allowing up to one preceding OR gives 2,449 distinct unions and 39,928 distinct products of a source with a union. A guard-masked union can be built from masked operands. AND of the union with itself or with its masked copy supplies an already OR-expressible source and leaves the original 160-clause optimum. The union itself may be used later without changing the clause language. After preloading the product, both its direct and masked copies are available.

The minimum residual clause count across these products is **exactly 129**. To verify the lower bound, each new source deletes the positive witnesses it distinguishes for a pair of negative rows. Pruning the endpoints of remaining broken pairs in the original 160-element packing gives a directly verified lower certificate. Only six product values have greedy packings below 129. Fresh certificates give exact optima of 133, 129, 132, 133, 141 and 142 for those six. The value wire[3] AND (wire[16] OR wire[20]) attains 129; its explicit clause cover is saved. The 64 raw exceptions and the six one-OR exceptions have independently replayable paired certificates.

Consequently any suffix computing the full test table with at most one OR before its first paid AND needs **at least nine paid ANDs including that first gate**, since seven remaining gates expand to only 128 clauses. An eight-paid implementation, if one exists, must use at least two ORs before the first paid gate. This bound applies even when all later OR and guard counts are unlimited. At two preceding ORs, wire[3] AND (wire[15] OR wire[16] OR wire[20]) has residual optimum 121. This gives a concrete limit of the clause-count argument; it does not construct a seven-paid suffix. The h=20 physical branch still allows nine further paid gates before preloading.

Discovery used SciPy MILP with 60 seconds for clique search and 120 seconds for covering, with relative gap zero. To discover the covers, start with all source bits and intersect with the complement of a negative signature whenever the allowed sources still hit every positive. Keep maximal rejectable negative sets, then cover all negatives with the fewest sets. The 38-positive core used a 20-second MILP. Integer upper and lower certificates, not solver bounds, determine the reported optima. On the 39,928-product scan, only the minimum, the 840 no-OR cases, and the explicitly matched exceptions are asserted exact.

## Physical 63-gate search

Fix h=20 and all 17 prefix gates, leaving 19 ORs, 18 guard ANDs and nine paid ANDs. For X=OR(11,14), the two nonempty third choices after Y=OR(4,13) are Z=OR(7,23) and Z=OR(23,42). There are also the two reverse orders. Width-16 packing on the 520 rows excludes all fourth columns (2,862 or 2,791 per triple; 11,306 in total counting across triples). Products involving Z are dominated by prefix values or previously excluded products. For the outstanding X/Y product with Y=OR(4,23), providing the product alone still requires at least 22 ORs against 19 available. Search used seed 3201, 40 randomized starts plus the initial choice per negative, three seconds per packing MILP and eight seconds per clique MILP. Certificates are checked on replay.

Cumulative exclusions reach 152 of the 230 first OR columns; 78 remain. With these cuts the single fixed X and the previously timed-out X/(4,13)/(7,23) triple each returned UNSAT in the 56-row CaDiCaL encoding with a 10-second limit. Use the parent report's SAT command with these additional gates. With the same 17-gate prefix and no fixed next OR, the 60-second run returned UNKNOWN on 56 encoded rows, with zero decoded candidates. The next open triple, X=OR(4,16), Y=OR(13,42), Z=OR(14,21), also returned UNKNOWN in 45 seconds on 56 encoded rows with zero decoded candidates. Resume with that triple. No unrestricted lower bound follows from these exclusions.

```sh
python research/order3_case35_clause_cover.py
python research/order3_case35_clause_preloads.py
python research/order3_case35_or_frontier.py 4 16
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneGuardedClauseExpansion.lean research/statements/PlaneGuardedClauseExpansion.txt check
```

The scoped desk returned not_open and issued no lease. The checked contribution is on the fork. PRs #7762 and #8170 remain merged with ACCEPTED checks and no review or inline change requests.
