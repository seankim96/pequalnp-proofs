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

## Uniform AND bound after gate six

In this same session the four-exception statement was combined with an endpoint certificate. For the same four fixed initial gates, **every choice at both gate five and gate six** leaves at least nine ANDs strictly in the free suffix, including a sixth gate that reads the fifth. There are 3,459,600 ordered choices. Both constants, repeated inputs, arbitrary fan-out and any output index are allowed in the tail. The theorem checks the 52 positive and 468 negative labels explicitly.

For clarity, assign to each of 52 flags a set of negative rows. Exclude a fixed set E. For every pair of remaining negative rows a,b, there is a flag assigned to a or b where every active baseline wire is also active on a or b. The actual assignment has 25 permanent exclusions, at most 46 rows per flag and covers all 97,903 pairs outside E. Dropping all rows assigned to the four possible exceptions costs at most 25 + 4·46 = 209 rows, leaving at least 259. The formal certificate uses the slightly looser E.card ≤ 27; this still leaves at least 257. On any surviving pair the four-exception theorem transfers the baseline witness to both newly added wires. Correctly separating 257 negatives requires at least nine ANDs, because eight binary trace bits supply only 256 traces.

For every AND/AND choice at gates five and six (864,900 ordered choices), the nineteen-OR lower bound after gate four also holds after gate six. The resulting total lower bound is **34** for this family. This does not rule out a circuit of size 63.

### Dependent sixth-gate search

For fifth OR(0,2), sixth AND(13,30) reads the fifth wire. The remaining 57 slots required at least nine ANDs and eighteen ORs. CaDiCaL 2.1.2 started from 52 positives and negatives 0 and 234, with 17,670 variables, 563,330 clauses and a 90-second wall budget for encoding/refinement and solving after initial construction. **UNKNOWN**; 54 rows encoded and zero candidates decoded.

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth OR 0 2 --sixth AND 13 30 --operator-bounds --all-positives --seconds 90 --solver /path/to/cadical

### Seventh gate handoff

With AND(13,26) and AND(13,27) fixed in either order at positions five and six, omit flags 0–3. Among 4,096 ordered seventh-gate choices, 3,856 introduce zero further exceptions and 240 introduce exactly one on the 520 tests. Exhausting all negative pairs, at worst 115 distinct higher endpoints are lost after omitting one further flag, and 140 after two further flags. This leaves 353 and 328 negatives, respectively. These seventh-gate results are finite numerical replay; the new uniform Lean theorem stops after the sixth gate.

    python3 research/order3_case35_sixth_charge.py
    python3 research/order3_case35_seventh_guard.py

### Uniform theorem verification and one-file comparison

**PlaneCase35SixthTraceBound — ACCEPTED (check), exit 0.** The pinned project checker rechecked 2,137 constants and reported propext, Quot.sound and Classical.choice. The manifest contains only this research module and the 87 upstream definition modules. The standalone file imports Mathlib. The pinned Lean compiler accepted its fully expanded statement, and a separate pinned leanchecker replay also exited 0. The proof counts traces directly on the subtype of retained negatives, using injectivity. The earlier prototype using the original unchunked column checks built in Lean, but its project verifier exited 137 without a verdict. The accepted version uses packed negative rows and smaller finite checks. The numerical replay reads the actual certificate words from the accepted source.

    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35SixthTraceBound.lean research/statements/PlaneCase35SixthTraceBound.txt check

Prepared one-file comparison against the verified upstream commit: https://github.com/seankim96/pequalnp-proofs/compare/ef366917e46626befd0942970384bccbe71cf018...eed33b78d21192b31c7a6ee9d2400c642cc20d85 . Branch: research/l-meta-2625-case35-all-sixth. The difference from the upstream base is one added Lean file. No upstream PR was opened for this research theorem; the parent desk entry has closed intake and its three reductions are present.
