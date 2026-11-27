# L-meta-2625 · Case 35, the point-seven star

Resumed from fork checkpoint `572f306c82eb5e30a4a7c4e19200cd5b98dc3f37`. The checked upstream base is `6df6ab83598b6505af0ab3abe10fd11ed33578f1`. The original 52 positive and 468 negative rows are unchanged. Upstream has the earlier reductions, and we found no accepted answer to the unrestricted 63-gate question. The desk reported the named unit unavailable and returned no lease for the scoped request. This is fork research. Author PRs #7762 and #8170 are merged with ACCEPTED checker comments and no requested edits.

## The fixed case and its remaining budget

Use 26 raw wires. The 13-gate prefix in physical order is OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24), AND(15,32), AND(25,32), AND(0,17), AND(0,23), AND(0,25). The completed point-seven prefix appends OR(17,19), OR(20,24), OR(39,40), AND(7,41). Write h for the total number of physical AND gates with wire 32 as an operand, counting a gate at most once. A paid AND has neither operand equal to wire 32. The 17-gate prefix contains two guard reads.

After gate 17 the lower bounds are eight paid ANDs, nineteen ORs, and, conditional on eight paid ANDs, twenty-two ORs. At h ≥ 21 at most 27 of the remaining 46 gates can be ORs or paid ANDs. Both alternatives exceed that limit. At h = 20 exactly nine paid ANDs, nineteen ORs and eighteen guard ANDs must remain. No witness is known for that boundary.

## Pinned Lean checks

Each contribution has one independent branch based directly on the checked upstream commit. The repository checker accepted each with only propext, Quot.sound and Classical.choice. For each file we also compared all 87 definition-module source digests to the base and compiled an independent example of the saved exact statement.

| Checked theorem | Scope | Kernel constants | One-file fork commit |
| --- | --- | ---: | --- |
| PlanePointSevenOrBudget | After only the first two point-seven ORs, accepting nineteen specified flags and rejecting negative 46 requires at least eighteen further ORs | 1840 | 135c47eb2cb3ce32045ea97f4000c3b3c29dbcfd |
| PlaneTightOrLeaves | An AND-closed family rules out a common live operand at a pivot and forces m ORs for width-m packings | 1755 | 7640c12162eecb7ddc664083a3b8459673aec19e |
| PlanePointSevenTightLeaves | After the three fixed ORs, at least nineteen additional ORs are required, with arbitrary later ANDs, wire reuse and output index | 1907 | 5a014ff40cf6c0179d7442a2cb86178e9b2bd958 |

For the last theorem the two width-19 packings use negatives 48 and 46, and pivot 11 is a required positive. A column is live for a packing when it is false on its negative and true on at least one of its flags. A separator using only eighteen ORs must spend all eighteen productively on both packings. Before the first OR true at the pivot, any signal true there has the value of an AND-only expression on the pivot-true starting columns, up to the AND-closed predicate used in the proof. The concrete wires 11 and 15 and their conjunction exhaust the pivot-true AND-only choices. Each fails at least one live test. The Lean statements contain the actual input masks and the complete fixed wiring.

## Replayed finite certificates

The four-arm star sweep covers 26 choices of center, each with three balanced and twelve nested OR trees (operand exchange and independent balanced child order identified). One ordinary packing after the three ORs has width 19 in 387 cases and width 18 in three. The pivot test raises the unconditional number of further ORs to 19 in 383 cases and 18 in the other seven. The independent 13-gate density bound requires at least 24 ORs if only eight paid gates follow that prefix. If there are nine or more, three fixed ORs plus these suffix bounds exclude h ≥ 23 for all 390, and h ≥ 22 for 383 even before selecting the center AND.

For the seven remaining trees, fix gate 17 to AND(center,41). All seven have a negative clique larger than 128 and, with eight paid gates remaining, require at least 22 further ORs. Four have 205 negatives (centers 2 and 6) and three have 167 negatives (center 9). Nine paid gates plus the unconditional eighteen ORs also exceed the 26 non-guard slots at h = 22. Thus every one of the 390 completed canonical stars excludes h ≥ 22. The comparison across all 390 uses executable integer certificates.

For point seven, the 160-negative clique has total flag width 2733. Each negative j needs at least its width minus one ORs false on j. With eight paid gates the freely oriented operand probes distinguish every clique member. A repeated physical probe in two receivers loses a bit, and an AND with identical operands is a copy. A paid output used as a later probe implies its source gate's chosen probe bit. For each such dependency select the earlier gate as parent. Enumerate all topologically ordered forests on eight gates, restricting the 256 words by their child-to-parent bit implications. Account for ORs only at the remaining roots.

There are 24 possible initial exceptional ports plus two placeholders for guard-AND outputs. A clique of 125 guard-false negatives confines all selected guard outputs to one receiving gate. For 323 of 325 pairs, explicit 65-negative cliques force the selected ports to share a receiver. Any triple includes at least two such pairs and would require a three-input gate. Orient each paid gate so each complete trace has at most one exceptional root. In every feasible forest the 160 lightest permissible words give at least 400 true entries after dropping any one root. Left and right orientations thus account for at least 800 true entries on distinct physical OR gates. The suffix OR floor is ceil((2733 + 800)/160) − 1 = 22.

The replay also computes a second conservative floor. On each feasible forest count all root bits, subtracting the maximum possible total cost of selected exceptional ports across both orientations. Each exceptional bit contributes at most its actual number of ones on the clique, capped at 128. The induced incompatibility graph on selected ports must have maximum degree one. The program checks both bounds, uses the stronger one, and verifies every clique, constant column and flag packing against the row masks.

## The open h = 20 boundary

There are 42 possible starting operands other than wire 32, giving 903 unordered pairs with repetition. If one of the nine paid ANDs computes the conjunction of such a pair, delete that gate and provide its output as an extra starting wire. Earlier and later uses of the other signals keep their values. A stronger starting signal, true on a superset of its positives and a subset of its negatives, also suffices by monotonicity. In 829 pairs an existing starting wire or constant false dominates the conjunction. Constant false changes no positive-pair witness or flag packing and cannot occupy a distinguishing probe port. For the remaining 74 pairs there are 71 distinct new columns. The per-column clique, packing and probe replay gives an OR floor of 21 or 22 with eight remaining paid gates. Across all 903, the counts by floor are 53 at 21 and 850 at 22. Each exceeds the nineteen-OR budget.

The same argument applies if either or both of those starting operands were first ANDed with the guard any number of times. After preloading their conjunction, a single guard AND produces the masked conjunction without consuming a paid gate or OR. If a stripped operand is itself the guard, the resulting conjunction is available from a starting wire and at most one guard AND. Thus every paid AND must take at least one wire beyond initial wires and their guard copies. In particular at least one new OR precedes the first paid AND. The stronger SAT cut marks all such guard copies, including ones created later in the circuit.

## Reproduction and solver log

Use the pinned Lean 4.36.0 toolchain. For each of the three names N above, run the base repository's checker with the contribution copied to its indicated source path and the statement from this fork.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/$N.lean research/statements/$N.txt check
python research/order3_case35_star_packings.py
python research/order3_case35_point_seven_probes.py
python research/order3_case35_star_preloads.py
```

The finite replay uses the stored families. Numerical optimization supplied candidate sets only. No optimizer status is used as a certificate. The sweeps check the starting columns on all 520 target rows. Solver runs start with 52 positives and four negatives, and any proposed circuit is replayed against all rows. Budgets below are solver seconds and exclude cut construction. UNSAT results with replayed cuts rely on their mathematical soundness. A timeout with zero decoded candidates is UNKNOWN.

Use the following common flags for point seven, then append the cut, optional extra gate, and solver budget from the table.

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads "$H" --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget --preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41
```

Append `--seconds B --solver /path/to/lean-4.36.0-linux/bin/cadical`. For the center-9 row replace gates 14–17 by OR(13,19), OR(21,39), OR(22,40), AND(9,41).

| Minimum h | Additional cut | Gate after 17 | Seconds | CaDiCaL result |
| ---: | --- | --- | ---: | --- |
| 24 | --star-packings | free | 10 | UNSAT |
| 23 | --star-packings | free | 10 | UNSAT |
| 22 | --star-packings | free | 90 | UNKNOWN |
| 22 | --star-packings | OR(1,2) | 10 | UNSAT |
| 22 | --star-packings | OR(0,3) | 60 | UNKNOWN |
| 22 | --star-leaves | free | 10 | UNSAT |
| 21 | --star-leaves | free | 70 | UNKNOWN |
| 21 | --star-probes | free | 10 | UNSAT |
| 20 | --star-probes | free | 120 | UNKNOWN |
| 22 | --star-probes, center 9 | free | 10 | UNSAT |
| 20 | --star-preloads | AND(27,41) | 10 | UNSAT |
| 20 | --star-preloads | AND(27,32), AND(41,43) | 10 | UNSAT |
| 20 | --star-preloads | free | 120 | UNKNOWN, 56 encoded rows and zero decoded candidates |

The open continuation is the completed point-seven prefix at h = 20 with the guarded-copy cut enabled. A next split is the first new OR and which of its outputs or descendants reaches a paid AND. Guard reads may precede that first OR. The h ≤ 19 continuations and the unrestricted 63-gate question also remain open.
