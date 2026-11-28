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
