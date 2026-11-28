# L-meta-2625 — A sixth ordinary AND after a point-pair OR

The research parent is 2bf8a5dd63cd8ef47f4039a51a55a24e90c96019. Use the same 17 physical gates of case 35, a total size of 63, exactly 19 physical ANDs reading guard wire 32, and the residual split of ten ordinary ANDs and nineteen ORs. Count suffix positions after skipping the guard ANDs. Fix the first three non-guard gates to A = AND(3,15), X = OR(12,42) and Y = OR(5,10) on the specified unmasked wires. The parent excluded ordinary AND at positions four and five. This checkpoint excludes it at position six for all choices of the fourth and fifth ORs. The computation uses all 52 positive and 468 negative rows.

## Enumeration and certificates

Let Z and W be the two as-yet unspecified ORs following Y, and let P be a candidate sixth ordinary AND. A path through a free guard mask counts as a dependence. If P ignores W, moving the predecessor closure through P forward gives the excluded order with an ordinary AND by position five. The same applies if P ignores Z. The moved computation can retain its physical gate counts by putting unused operations later and relabelling in topological order. The parent exclusion applies to every pair of ORs after A,X.

When Z and W are independent, the normalized AND must read both. Enumerate all unordered pairs of possible OR columns, allowing equality. When W depends on Z, W can read raw Z or its guard mask. The normalized product is W AND an older wire, W AND Z, or W itself. A masked operand adds an optional final guard mask. If a column has both independent and dependent derivations, both cases enter the census. The verifier uses the full enumeration, including branches in which an operation could have been moved earlier.

Preload two relaxed columns that supply A and P by signed dominance, optionally after a guard mask. A replacement must include every positive bit of the replaced wire and introduce no negative bit outside it. The prefix and the ORs are available in their original order. Deleting the two paid ANDs leaves at most eight ordinary ANDs and nineteen ORs in the relaxation. An integer certificate requiring at least twenty ORs excludes the candidate product. If P is already supplied by an available wire or its mask, only the preload for A is needed to delete both ANDs. This is a numerical exclusion for one suffix budget.

For Y = OR(5,10) there are 2,724 possible Z columns, 3,711,450 unordered independent pairs, and 1,083,320 distinct nonredundant product columns before applying the inherited certificates. Replaying the parent leaves 1,185 independent products. In the dependent enumeration, 344,823 ordered (Z,W) choices leave 1,078 surviving (Z,W,P) triples on 379 distinct products. Across both branches, 667 signed-maximal representatives suffice. All 667 new witness pools have a verified OR floor of at least 20. Six needed strengthened integer witnesses. Replaying the final census leaves zero independent products and zero dependent triples. The previous fixed-fourth result is now valid for every fourth OR in this branch.

Each negative-clique optimization used an eight-second HiGHS budget. The per-negative packing optimizations on the 52 positive flags had no separate time limit. Only feasible integer witnesses enter the ledgers. The digests in the census module verify every compressed witness file before replay. Re-run from the root of the research checkout:

```sh
python research/order3_case35_h19_sixth_after_third.py --partner 10 --parent-cache /tmp/case35-parent.json
```

A separate CaDiCaL query fixed the physical prefix through A,X,Y and then OR(0,45), OR(4,46), AND(14,47). It allowed at least nineteen guard reads and did not fix the ordinary gate split. The 90-second query used all positives and negative seeds 1 and 2 (56 encoded rows) and returned UNKNOWN with zero decoded candidates. To reproduce, use the direct command in the least-guard-preload checkpoint through OR(12,42), replacing the final gates with these four gates starting at Y. The solver timeout contributes no exclusion.

The project desk returned no lease for L-meta-2625. The public lemma metadata lists it as a conjecture. The checked upstream tree at 3f0d56fe04bbc3c4f4ea413196470e29d1cffce8 contains three reductions and no direct solution. PRs #7762 and #8170 are merged and have no outstanding review changes. The unrestricted 63-gate target remains open.

## Kernel-checked reordering lemma

PlaneCommuteIndependentBlock moves one named binary Boolean gate across a list of gates with distinct output from that gate and no reads of each other's output across the move. The gates in the list may depend on one another. For every initial state and every common trailing schedule, the two schedules produce equal values on every wire. The proof exchanges adjacent independent writes and inducts over the list. This establishes the state-preservation step on fixed wire labels; the numerical dominance certificates and their enumeration are separate.

The official checker using the pinned Lean 4.36.0 accepted the exact research statement, rechecking 1,715 constants with propext and Quot.sound. All 87 definition digests matched upstream 3f0d56fe04bbc3c4f4ea413196470e29d1cffce8. A separate Lean import elaborated the exact type and printed the same axiom list. The proof-only fork commit 3f1015e75b15202fadaa4e2d29ed8bd13ae9a15f differs from its upstream parent by exactly one Lean source file.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCommuteIndependentBlock.lean research/statements/PlaneCommuteIndependentBlock.txt check
```

## Extending ten branches through the seventh non-guard position

Within Y = OR(5,10), fix fourth gate Z = OR(0,Y) and fifth gate W = OR(i,Z), where i ranges over 1, 2, 3, 4, 6, 7, 8, 9, 11 and 12. The sixth operation can be any OR V of available operands, including masked operands. If a seventh ordinary AND has no dependency on V, it can be advanced to position six, already excluded for this Y. If it does depend on V, normalize the product to V AND an old operand, up to a final guard mask. A self-product copies V and can be deleted.

The ten cases have 29,772 sixth-OR choices counted per case. With the seed certificates, 977 (V,P) pairs remain, with 883 distinct P columns across the ten cases. There are 585 signed-maximal representatives. The verified OR floors on their two-preload pools are 20 on 11, 21 on 185 and 22 on 389. All ten final residual pair counts are zero. The passing-order condition in these ten branches now requires an OR at position seven as well. The eighth position and the other choices of Z and W remain available for investigation.

The extra discovery pass was checked against a full enumeration using the original ordered physical prefix, with guard wire 32. Only records used by the 585 representatives in this enumeration are included. Every compressed witness was matched to its independently replayed integer certificate.

```sh
python research/order3_case35_h19_seventh_point_chain.py --parent-cache /tmp/case35-parent.json
```

At i=4, fixing V = OR(14,47) and P = AND(1,48) in the broader direct SAT search gave UNKNOWN at 120 seconds, on 56 encoded rows and zero decoded candidates. Reproduce with the direct 90-second command above, replacing its final AND(14,47) by OR(14,47), AND(1,48) and using a 120-second limit.

## Replaying the direct SAT queries

Use Bash at the research checkout root with the pinned Lean toolchain active. Each run also enforces the 63-gate size from case 35.

```bash
common=(
  --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26
  --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32
  --tenth AND 25 32 --eleventh AND 0 17 --twelfth AND 0 23
  --thirteenth AND 0 25 --fourteenth OR 17 19 --fifteenth OR 20 24
  --after-fifteen OR 39 40 --after-fifteen AND 7 41
  --after-fifteen AND 3 15 --after-fifteen OR 12 42
  --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds
  --shared-guard-budget --min-guard-reads 19 --wire-credit --adaptive-charge
  --trace-budget --preloaded-trace --guard-read-ceiling --or-trace-density --star-probes
  --solver "$(lean --print-prefix)/bin/cadical"
)
chain=(--after-fifteen OR 5 10 --after-fifteen OR 0 45 --after-fifteen OR 4 46)
python research/order3_prefix_search.py "${common[@]}" "${chain[@]}" --after-fifteen AND 14 47 --seconds 90
python research/order3_prefix_search.py "${common[@]}" "${chain[@]}" --after-fifteen OR 14 47 --after-fifteen AND 1 48 --seconds 120
python research/order3_prefix_search.py "${common[@]}" --after-fifteen OR 0 2 --seconds 60
```

## All twelve third-point partners for point 5

Keep A and X and replace Y by OR(5,i) on the original point-input wires for every i from 0 to 12 other than 5. In all twelve branches the sixth non-guard operation must be another OR. Neither the fourth nor the fifth OR is fixed. The restrictions on the physical prefix, total size, guard reads and remaining gate split still apply.

The full census covers 44,401,378 unordered independent pairs and 4,126,957 dependent OR pairs, counted per third-point choice. After applying the inherited certificates and the seed-10 certificates there were 14,877 distinct product columns across the family. The full enumerations agree with a separate discovery pass restricted to products that genuinely depend on the third OR. The 4,995 additional signed-maximal representatives have the following checked floor distribution: 20 ORs on 343 pools, 21 ORs on 2,255 pools, 22 ORs on 2,397 pools. Of the 4,995, 22 needed strengthened integer witnesses. Each packaged witness was independently checked and compared with its source record.

| Third partner | Possible Z values | Independent residual products after seed | Dependent residual triples after seed | Distinct products in either residual | Final residual products |
|---:|---:|---:|---:|---:|---:|
| 0 | 2,715 | 1,403 | 1,561 | 1,780 | 0 |
| 1 | 2,714 | 1,182 | 1,044 | 1,451 | 0 |
| 2 | 2,723 | 1,514 | 1,661 | 1,893 | 0 |
| 3 | 2,717 | 1,252 | 1,246 | 1,555 | 0 |
| 4 | 2,724 | 1,340 | 1,398 | 1,689 | 0 |
| 6 | 2,721 | 1,525 | 1,655 | 1,904 | 0 |
| 7 | 2,718 | 1,271 | 1,050 | 1,547 | 0 |
| 8 | 2,724 | 1,173 | 1,015 | 1,445 | 0 |
| 9 | 2,713 | 1,407 | 1,219 | 1,706 | 0 |
| 10 | 2,724 | 0 | 0 | 0 | 0 |
| 11 | 2,724 | 1,169 | 1,039 | 1,443 | 0 |
| 12 | 2,721 | 1,067 | 867 | 1,301 | 0 |

Run the full family with `python research/order3_case35_h19_sixth_after_third.py --parent-cache /tmp/case35-parent.json`. The cached parent is accepted only when its digest matches the 5,676 previously verified pools.

## Handoff for Y = OR(0,2)

The third OR here reads original point wires 0 and 2. The fourth and fifth ORs are free. There are 2,714 possible fourth OR columns, 3,684,255 unordered independent pairs, and 342,475 dependent OR pairs. Before the extra high-positive-support certificates, the sixth-AND frontier had 1,444 independent and 748 dependent products, with 2,083 distinct values in the union. Among these, 166 product columns were true on at least nine of the 52 positives. Their 83 signed-maximal representatives were certified at OR floors of 21 (six pools) or 22 (77 pools).

After those certificates, 1,272 independent products and 718 dependent products survive; the dependent products occur in 2,899 triples. Their union contains 1,899 products on three to eight positives, with 561 signed-maximal values. This is the next unfinished sixth-position case. A surviving column is only a candidate, not a satisfying circuit. The 60-second direct SAT query fixing A,X,OR(0,2) with at least nineteen guard reads returned UNKNOWN on 56 encoded rows and decoded no candidate.

The exact sorted lists are in `case35-h19-0-2-sixth-frontier-47.json.gz`. The SHA-256 of the uncompressed JSON is `68d22bb3f42aa7b7d809b427298612c455616fcfcab7781a0617f06289808b7c`. Regenerate from the research checkout:

```sh
python research/order3_case35_h19_sixth_after_third.py --explore-pair 0 2 --parent-cache /tmp/case35-parent.json --write-frontier /tmp/sixth-0-2.json
sha256sum /tmp/sixth-0-2.json
```

The later project snapshot at 2026-11-28 10:14:22 UTC still reports L-meta-2625 as a conjecture. Upstream commit 3f9d4b05338a269fbd2e6a9170b6c5ab2cba3bf9 still has reductions 50, 317 and 487. The pinned configuration, official checker and project definition sources match the checked upstream base. The 5,676 inherited pool ranks were replayed from their original ledgers in this session and matched the cache byte for byte. A clean invocation of the published seed verifier and a separate invocation of the published seventh-position verifier returned empty residuals.
