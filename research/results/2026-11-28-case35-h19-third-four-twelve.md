# L-meta-2625 case 35, sixth ordinary AND after OR(4,12)

Parent a8459b8e1c94e5c7ed8ace711aa875a15cc4e398 left 638 distinct products and 309 signed-maximal representatives. Hold the original 17-gate prefix, total size 63, exactly 19 physical reads of guard wire 32, ten ordinary ANDs and nineteen ORs in the suffix. After excluding guard ANDs from the position count, fix the first three ordinary gates to AND(3,15), OR(12,42), OR(4,12). Positions four and five may be any ORs, including one reading the other or a guarded operand. Test a sixth ordinary AND on the 52 positive and 468 negative rows.

Every remaining representative obtained an independently replayed integer certificate. OR floors were 20 for 10 pools, 21 for 200 pools and 22 for 99 pools. Each exceeds the budget of 19. Each pool supplies the first and the candidate AND by signed dominance, allowing the shared guard. Singleton discovery used the parent envelope construction, an eight-second HiGHS negative-clique limit per optimization, and no separate per-call positive-packing deadline. Only replayed witnesses enter the ledger. No grouped certificates were needed.

Filtering the committed frontier leaves zero. Fresh enumeration checked 3,342,405 common independent pairs, 3,703,281 independent pairs in total for this third column, and 344,143 dependent OR pairs. Both residual sets were empty. This is a finite certificate-backed exclusion under the stated constraints.

Across the 78 raw third point pairs, 37 are now excluded and 41 retain products. Among the 2,585 possible third columns, earlier-wire or resolved raw-pair substitutions cover 1,245. The smallest remaining raw pair is OR(9,12). Refiltering the archived baseline and independently enumerating that pair produced identical bytes. Its 872 independent and 257 dependent product values have a union of 1,073, including 467 signed-maximal representatives. Its uncompressed SHA-256 is 3d25a4894a01c2bc2191d00fbf5729da397ca0186118f3270377ee29971b4b57.

To replay the closure in the fork checkout, use the following command. An absent parent cache is regenerated from the inherited certificates.

```sh
python research/order3_case35_h19_third_four_twelve.py --parent-cache /tmp/case35-parent.json
```

Direct CEGAR runs used CaDiCaL from the pinned Lean 4.36.0 distribution and the common arguments in the parent report. After A,X the fixed continuation OR(4,12), OR(0,45), OR(7,46), AND(14,47) timed out at 45 seconds. OR(9,12) alone timed out at 60 seconds. Both returned UNKNOWN, 56 encoded rows and zero decoded candidates. These queries allow at least 19 guard reads without fixing the ordinary split.

The public snapshot at 2026-11-28 11:28 UTC marks the unrestricted unit as a conjecture. Upstream 17504801b50c8a038e95149c91fa3ce63dab38e6 retains reductions 50, 317 and 487. The targeted desk issued no lease. Both account PRs 7762 and 8170 were merged and accepted, with no outstanding changes.

## Closing the subsequent OR(9,12) branch

Starting from the SHA-256 above, the 467 signed-maximal representatives of the 1,073 remaining products generated 467 independently replayed pools under the same budgets. Of these, 465 used the basic integer packing and two used the strengthened compatibility witnesses. Their OR floors are 20 for 25 pools, 21 for 224 pools, and 22 for 218 pools. All are above 19. The independent and dependent residuals are both empty in a fresh enumeration of 3,673,405 independent pairs and 341,974 dependent pairs. The replay command above now checks both closures in order.

The cumulative result is 38 resolved raw third point pairs out of 78. With earlier-wire substitutions, 1,246 of the 2,585 possible third columns are excluded for a sixth ordinary AND. The next raw third OR is **OR(0,12)**. Fresh enumeration of its 3,678,828 independent pairs and 342,236 dependent pairs agrees exactly with refiltering its earlier frontier. There are 744 distinct independent products and 349 dependent products, with 1,048 in their union and 448 signed-maximal representatives. The updated frontier in `case35-h19-0-12-sixth-frontier-49.json.gz` has uncompressed SHA-256 `6668540e7e91efd1487272103df0f705589ed31210fa53469ecae45b34548000`.

The closures apply to the stated fixed prefix and gate budget. The project still listed the unrestricted 63-gate question as a conjecture at its 2026-11-28 11:37:25 UTC snapshot.
