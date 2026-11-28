# L-meta-2625 — Absorbed ANDs and the next gate in case 35

Research parent f9419b8622b7479cf1569292bdd52c3f027a7848. Upstream snapshot 033d50c85039173e65cc7a0a956606ef2e3fd005 contains three reductions (50, 317 and 487) and no completed unrestricted result for this unit. The desk returned no lease for this gap. There was no lease to renew or release. PRs #7762 and #8170 are merged, with no open review threads. No upstream PR was opened.

## Lean result independent of the physical prefix

The pinned Lean 4.36.0 checker accepted PEqualNP.Research.PlaneAbsorbedAnd and rechecked 1,731 constants. All 87 project definition hashes in the manifest match the upstream snapshot. A separately elaborated example checked the exact expanded statement against the theorem. Its reported axioms are propext, Classical.choice and Quot.sound. The single-file fork branch research/l-meta-2625-absorbed-and has commit 4d5285bbd644a0cb3947897a6a03acbf7255b42b.

For any monotone fan-in-at-most-two circuit, split its gate list at a binary AND with inputs i,j. Suppose that on every prescribed negative input where wire i is true, wire j is true as well. Replace that gate by a unary OR copying i. The prefix is identical, and every later wire has the same value on the prescribed negatives. On positives the value can only increase through each subsequent monotone gate. Thus the modified circuit separates the same positive and negative families, is still monotone and has exactly the same size. This removes one distinct-input AND when i differs from j, while keeping wire indices valid for all subsequent references. It supplies the absorption step in the nine-AND enumeration at the parent checkpoint. The finite orbit enumeration and the unrestricted 63-gate lower bound remain separate obligations.

## Integer certificates on the 520 desk tests

Use the parent's 17-gate case-35 prefix (PREFIX13 + POINT7). Fix exactly 19 guard reads in the 63-gate circuit and the (9 ordinary AND, 20 OR) suffix budget after gate 17. Append OR(14,18) at wire 43 and AND(1,43) at wire 44. The suffix now has eight ordinary ANDs, 19 ORs and 17 guard-reading ANDs. An ordinary gate here means an operation other than AND with physical wire 32. The tests are the 52 positives and 468 negatives returned by order3_prefix_search.test_rows().

**The next non-guard gate cannot be an AND.** Before that gate, the only possible operands are starting wires and their copies masked by the guard. It suffices to provide their unmasked product in advance. Guard ANDs are free in the relaxed problem and can recover the masked product. A guard-only operand yields a free mask of the other operand; its self-product is covered by a repeated-index pair. The 44 non-guard starting wires give 990 pairs with repetition and 592 distinct products. With a product provided for free, at most seven ordinary ANDs and 19 ORs remain.

* For 547 products (944 physical pairs), a clique of 129 pairwise incompatible negatives requires more than seven observation bits. For each pair, a positive witness lies beneath the bitwise union of the two rows, and a guard-true witness requires both guards true.
* For the remaining 45 products (46 pairs), all 468 negatives admit an explicit proper 128-coloring. The clique-only approach cannot exclude them. The separate density certificates give an OR floor of 23 for each of these products.
* Each density certificate contains a clique of k = 116 to 128 negatives, positive-flag packings on those rows, a 65-row guard-false clique and a constant 65-row clique for **every** starting column. Choosing one operand independently per ordinary AND must yield distinct seven-bit words on each clique. A starting wire or guard-masked wire in a probe would permit at most 64 words on its constant clique. If a probe were an earlier ordinary AND output, choosing either operand of its parent induces a bit implication, allowing at most 96 distinct words on the k-clique. Reusing a wire at distinct receivers would allow at most 64 words; duplicating it in a single gate would make that gate a removable copy. Hence all 14 operand ports must be distinct OR outputs.
* For each negative j the packing width f_j requires at least f_j−1 ORs false on j by the existing packing bound. Observing all left ports, then all right ports, counts at least twice the total weight of the k lightest seven-bit words in true OR entries. Summing false and true entries gives the replayed integer floor of 23. Both the 129-clique test and the OR-floor test work with arbitrarily many guarding ANDs.

The 45 graph colorings are independently checked edge by edge. The source accepts an exclusion only after validating the product domain, clique edges, every packing, the constant families, and the budget arithmetic. These are computational certificates for a restricted family; the Lean theorem above verifies the distinct normalization operation.

## Next OR choices and solver limits

With the same fixed prefix, the next OR may join any two of 76 distinct starting or guard-masked columns. These give 2,656 different unions. Of those, 1,383 are dominated on the labels by a free starting or guard-masked wire. Removing this OR would leave 18 ORs against the parent's verified floor of 19. For further exclusions the script prepays the specific next OR, leaving eight ordinary ANDs and 18 ORs, and replays the packing and probe bounds for that extended pool. The exact counts and continuation point follow below.

The direct CaDiCaL test for the further gate OR(0,44), with at least 19 guard reads and no fixed suffix operator split, timed out in 45 seconds on 56 encoded rows with zero candidates. Verdict UNKNOWN for that broader query. An integer certificate separately excludes this OR in the exact (9,20) budget at h = 19. A 180-second multi-objective attempt at the whole exceptional order timed out (UNKNOWN). A seed-3939 width-19 packing search using 40 randomized objectives and three seconds per MILP generated no exclusions.

Discovery of the 129-cliques was deterministic greedy search. Residual maximum-clique MILPs were limited to five seconds each; 128-coloring SAT instances used two seconds apiece with pinned CaDiCaL and produced 45 color assignments. For seven-bit density, row-packing MILPs had a two-second limit and weighted clique MILPs five seconds per objective. For the first eight-bit OR-floor sweep, clique MILPs had eight seconds each and individual 52-variable packing MILPs had no separate timeout. A failed heuristic or timeout never establishes infeasibility. The replay scripts use the saved integer witnesses without either MILP or SAT.

Reproduce from the repository root:

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneAbsorbedAnd.lean research/statements/PlaneAbsorbedAnd.txt check
python research/order3_case35_h19_second_product.py
python research/order3_case35_h19_second_or.py
```

**Replay verdict for ORs.** Sixty-one additional distinct OR values have an eight-AND certificate giving a floor of 19, bringing the total excluded to 1,444 of 2,656. The 61 came from testing the first 36 non-dominated candidates ordered by OR(0,44) first and then decreasing negative weight and column value ascending, followed by the remaining 48 untested non-dominated unions with wire 44 or its guard mask as a source. There are 147 such wire-44 union values, with 129 excluded and 18 still open under these tests. On those 18 an additional sweep used four packing-weight objectives with cutoffs 0, 13, 10 and 15, clique MILP limits of eight seconds, and a 100-second batch budget. It completed without a stronger certificate.

**Resume.** The OR replay returns the exact set of 1,212 unexcluded values so that future runs can skip all excluded cases. OR(4,44) is a specific unresolved choice in the 18-element subgroup. For an unrestricted attack on the number of ordinary ANDs, formalizing the OR-support normal form and the finite symmetry enumeration are still open. The separate (10,19) budget at h = 19 and the general 63-gate question remain open.
