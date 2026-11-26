# L-meta-2625 — the sixth gate in case 35

Starting fork commit: 3f8837e107a24ca28a26f42fac8a59217d63906f. Upstream checkout: ef366917e46626befd0942970384bccbe71cf018. Pinned toolchain: leanprover/lean4:v4.36.0.

## Checked results

The first four gates are OR(0,1), OR(3,9), AND(15,27), AND(17,26), with the 26 raw inputs numbered from zero. The target rows are the 52 positive flags and 468 negative tests from the parent checkpoint.

* **PlaneCase35SixthExceptions — ACCEPTED (check), exit 0, 1,769 constants.** For either operator and every ordered pair of earlier operands at gates five and six (including repeated wires and reads of gate five), the joint exception set has size at most four. Outside it, whenever either new wire is on at a positive row, a specific pre-five wire is on there and implies that new wire on every natural row index. The theorem covers 1,800 × 1,922 = 3,459,600 ordered extensions. In the dependent OR-then-AND case, distributivity reduces the sixth wire to the OR of two old-wire intersections. This proves the structural part of the previous numerical observation.
* **PlaneCase35SixthSparseBudget — ACCEPTED (check), exit 0, 2,004 constants.** Place AND(13,26) and AND(13,27) in positions five and six in either order. Their positive supports are {0,1} and {2,3}. Any completing suffix has at least nine AND gates. The proof uses 257 pairwise-separated negative rows and still holds if extra starting wires satisfy the stated inheritance condition. Constants are allowed in the tail, and the output may be any wire. Since the previous nineteen-OR bound after gate four still applies and both additional gates are AND, at least **34 total gates** are necessary in these two orders.

Both proofs import only Mathlib. Their checker manifests matched the fork source and all 87 definition modules at the upstream checkout. Both axiom lists consist of propext, Quot.sound and Classical.choice. Reproduce from a checkout with the pinned dependencies:

    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35SixthExceptions.lean research/statements/PlaneCase35SixthExceptions.txt check
    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35SixthSparseBudget.lean research/statements/PlaneCase35SixthSparseBudget.txt check

## Search and desk

Case 35, gates five and six AND(13,26), AND(13,27), followed by 57 free gates. Required suffix counts: at least nine AND and nineteen OR. CaDiCaL 2.1.2, 90-second solving/refinement budget, all 52 positives plus negatives 0 and 234 initially encoded. Initial CNF: 17,727 variables and 563,444 clauses. **UNKNOWN**, 54 encoded rows, zero decoded candidates. This provides no 63-gate witness or UNSAT certificate.

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --operator-bounds --all-positives --seconds 90 --solver /path/to/cadical

The public desk returned not_open for L-meta-2625. Upstream still has its three reductions and the unrestricted 63-gate question has no identified resolution. The five prepared assignment branches were checked. All four upstream PRs by seankim96 are closed, and #7762 and #8170 are merged with ACCEPTED intake and no requested review changes. No standard lease was taken, renewed, or released. The fork contains this checkpoint.
