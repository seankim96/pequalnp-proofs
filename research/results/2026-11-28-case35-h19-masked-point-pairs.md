# L-meta-2625 — Closing the remaining sixth AND after OR(0,2)

Parent research commit cedac677b67476d2aadcb96861017baab300b83c. The project's 2026-11-28 10:20:39 UTC snapshot still lists L-meta-2625 as a conjecture. Upstream 8b3771bb237ff5671e3d9dc90f7cfc002ad34183 contains the three existing reductions 50, 317 and 487. The targeted desk returned no lease. The account has no open upstream PR, and both #7762 and #8170 have merged with accepted checks and no requested changes.

Use case 35's original 17 physical gates, total size 63, exactly nineteen physical reads of guard wire 32, ten ordinary ANDs and nineteen ORs in the suffix. Positions below skip physical guard ANDs. Fix A = AND(3,15), X = OR(12,42) and Y = OR(0,2), followed by any two ORs. The sixth non-guard gate must also be an OR. This is a restricted, certificate-backed numerical exclusion on all 52 positive and 468 negative inputs.

The previous frontier had 1,899 distinct candidate products. Its SHA-256 was verified before selecting 561 signed-maximal representatives. For each representative P, two preloaded columns can supply A and P, directly or after a guard mask. The relaxation retains eight ordinary ANDs and nineteen ORs. The independently replayed integer OR floors were 20 for two pools, 21 for 51 pools, and 22 for 508 pools. The union of the independent and dependent residuals fell from 1,899 to zero. Another 111 replayed certificates target input-masked variants of the third OR. The two compressed ledgers contain all 672 records.

For the direct SAT cross-check use the three-query Bash recipe in the parent report, retaining `common` and fixing the following gates. This query permits at least nineteen guard reads, without the fixed ordinary split. Pinned CaDiCaL at 75 seconds returned UNKNOWN with 56 encoded rows and no decoded candidate.

```sh
python research/order3_prefix_search.py "${common[@]}" --after-fifteen OR 0 2 --after-fifteen OR 4 45 --after-fifteen OR 7 46 --after-fifteen AND 14 47 --seconds 75
```

Negative-clique discovery used an eight-second limit per HiGHS optimization. The per-negative packing on the 52 positive flags had no separate solver deadline. Only independently replayed integer witnesses count. To replay the certificates and the exact parent frontier, run the following command in the research checkout. An absent cache is regenerated from the inherited witness ledgers.

```sh
python research/order3_case35_h19_masked_point_pairs.py --parent-cache /tmp/case35-parent-48.json
```
