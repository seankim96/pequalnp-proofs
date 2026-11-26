# L-meta-2625 — nine ANDs strictly after gate eight

Research parent a71bb751286c2e06ed21750270a108fff3def402. Upstream verification base 982e0733951c7f572dbc695fc4a38e4ca8408222. Toolchain leanprover/lean4:v4.36.0.

## Scope

In case 35 fix OR(0,1), OR(3,9), AND(15,27), AND(17,26). Place AND(13,26) and AND(13,27) at gates five and six in either order. Gate seven ranges over both operators and all ordered pairs of the 32 existing wires. Gate eight ranges over both operators and all ordered pairs of the 33 existing wires, including the output of gate seven. Constants false and true are also available throughout the completing tail; it may choose any wire as output. Agreement with all 52 positive and 468 negative rows forces at least nine ANDs in the tail strictly after gate seven (first theorem) or strictly after gate eight (second theorem).

* Seventh-gate scope: 4,096 ordered choices. If gate seven is AND, the existing nineteen-OR bound strictly after gate four gives at least 7 + 9 + 19 = 35 total gates.
* Eighth-gate scope: 8,921,088 ordered choices. If both gates seven and eight are AND, all nineteen ORs remain necessary, giving **36 total gates** for these 2,230,272 ordered extensions. This counts the corresponding actual wire order. No statement in this session excludes an unrestricted size-63 circuit.

## Proof

The new fixed wires are inactive on positive flags 4–51. On those positives, an AND of two wires from the 32-wire pool either equals a parent on all rows, or accepts at most one exceptional flag. The classification reduces the old-wire case to the verified 30-wire pair-shape theorem. If either input is new, inactivity suffices. A seventh OR inherits its parents' separation witnesses.

Two free gates introduce at most two additional exceptional flags outside flags 0–3. When the eighth AND reads a seventh OR and an old wire, distributivity represents its output as the OR of two old-wire intersections. When the seventh gate is AND, intersecting again either reduces to another old-wire intersection or remains confined to its exceptional flag. Idempotence handles a duplicated gate-seven operand. The proof quantifies over both wire orders without enumerating the eight million circuits in Lean.

The endpoint certificate permanently removes 96 negative rows. For each of the 52 positive flags it assigns at most 45 further negatives; flags 0–3 get no assignments. For every distinct pair among the remaining 372 negatives, an assigned positive flag witnesses separation by the first 30 wires. Excluding one further flag therefore keeps at least 327 negatives; excluding two keeps at least 282. The seventh and eighth wires preserve the witness on every surviving pair. Distinct surviving negatives require distinct AND traces: eight AND gates provide only 256 traces.

Independent replay checked all 69,006 pairs of retained negatives. The ordered seventh/eighth choices had 0, 1 and 2 further exceptions in 7,907,648, 983,776 and 29,664 cases, respectively.

## Solver experiments

CaDiCaL 2.1.2, full 520-test synthesis problem, 63 binary gates total without constants. Each run started from all 52 positives and negatives 0 and 234. The 90-second limit starts after building the initial clauses and includes DIMACS writing, solving, decoding and refinement. Both returns were UNKNOWN. These time-bounded runs yielded no valid circuit and no UNSAT certificate.

| Fixed seventh/eighth gates | Free slots | Minimum suffix AND/OR | Initial variables/clauses | First run |
|---|---:|---|---|---|
| AND(0,17) / free | 56 | 9 / 19 | 17,472 / 553,560 | UNKNOWN, 54 rows, 0 candidates |
| OR(0,2) / AND(13,32) | 55 | 9 / 18 | 17,160 / 543,566 | UNKNOWN, 56 rows, 1 rejected candidate |

Both runs used case 35 with fifth AND(13,26) then sixth AND(13,27). The second eighth gate reads the seventh. Reproduce from the fork root:

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh AND 0 17 --operator-bounds --all-positives --seconds 90 --solver /path/to/cadical
    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 0 2 --eighth AND 13 32 --operator-bounds --all-positives --seconds 90 --solver /path/to/cadical
    python3 research/order3_case35_eighth_guard.py
    python3 research/order3_case35_seventh_guard.py

For gate nine, the exact higher-endpoint enumeration now covers every triple and quadruple of additional omissions among flags 4–51. The worst triple costs 168 negatives (example 5,6,7), and the worst quadruple costs 188 (example 5,6,7,42). At least 300 and 280 negatives respectively survive. These are Python checks of 17,296 and 194,580 masks, respectively. To extend the uniform suffix theorem another gate, prove a suitable structural exception bound for three free gates and certify the larger omission family.

## Intake

The desk reported not_open for L-meta-2625. Upstream main contains R_meta_2625_50, _317 and _487. No direct unrestricted verdict was located. All four PRs by seankim96 are closed; #7762 and #8170 are merged with ACCEPTED intake, no pending review requests, reviews or inline comments. Checked all existing fork heads, including the prepared sixth-gate contribution. No standard lease was taken or modified. Work is checkpointed on the research fork.

## Verification and prepared contribution

The pinned repository checker returned **ACCEPTED (check), exit 0** for both independent one-file theorems. It rechecked 2,130 kernel constants for PlaneCase35SeventhTraceBound and 2,144 for PlaneCase35EighthTraceBound. Each manifest included its single proof source and 87 verified upstream definition modules. The axiom lists contain propext, Quot.sound and Classical.choice. Both expanded statements separately passed the pinned Lean compiler and leanchecker replay, exit 0. Ten operator-threshold regression cases exercised the strengthened branches and their fallbacks. An initial seventh-gate draft omitted the lower bound on the witness index in a helper statement, which was corrected before acceptance.

    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35SeventhTraceBound.lean research/statements/PlaneCase35SeventhTraceBound.txt check
    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35EighthTraceBound.lean research/statements/PlaneCase35EighthTraceBound.txt check

Prepared one-file comparison: https://github.com/seankim96/pequalnp-proofs/compare/982e0733951c7f572dbc695fc4a38e4ca8408222...337f028530838a572d85cf5087697278348d487c . No upstream PR was opened for this restricted-prefix theorem while the desk entry is closed.

The dependent eighth-gate search was repeated for 90 seconds (UNKNOWN, 54 rows, no decoded model) and 180 seconds (UNKNOWN, 56 rows, one decoded model). The 180-second candidate accepted all positives but incorrectly accepted 460 of 468 negatives. Its only correctly rejected negative indices were 0, 112, 114, 167, 169, 183, 228, 234. Adding the first two failing indices as starting rows with `--negative-seed 1 --negative-seed 2` gives a reproducible next starting point. A fresh 60-second run from those 56 rows returned UNKNOWN with no decoded candidate.

## Ninth-gate extension on four eight-gate prefixes

Fix gates seven and eight to AND(0,17) and AND(0,23) in either order, independently of the earlier swap at five and six. The added exceptional flags are 16 and 40. Transfer all negatives charged to either flag into the permanent exclusion set, increasing its size from 96 to 162. The remaining charges are the original bitboards intersected with the surviving negatives. Outside flags 0–3,16,40, the four fixed added wires are all false on positives. Any ninth gate using these 34 wires introduces at most one further exceptional flag; its charge costs at most 45 rows. Hence at least 261 negatives remain, again forcing nine ANDs strictly after gate nine. There are 9,248 ordered choices across the four prefixes. For the 4,624 choices with an AND ninth gate, the established nineteen-OR bound yields **at least 37 gates total**.

A separate 90-second CaDiCaL search fixed gates seven, eight and nine to AND(0,17), AND(0,23), AND(1,14) in that order. With 54 free gates, at least nine ANDs and nineteen ORs in the suffix, the initial 54-row formula contained 16,956 variables and 533,792 clauses. Outcome UNKNOWN with 54 encoded rows and no decoded candidate.

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh AND 0 17 --eighth AND 0 23 --ninth AND 1 14 --all-positives --operator-bounds --seconds 90 --solver /path/to/cadical
    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35NinthTraceBound.lean research/statements/PlaneCase35NinthTraceBound.txt check

The stronger unrestricted choice of gates seven through nine remains open in this research branch. Numerical preparation now covers every set of five additional omitted flags beyond flags 0–3. Simple removal of higher endpoints works for 1,712,296 of the 1,712,304 five-flag masks. For the eight exceptions a deterministic greedy vertex cover removes 187–198 of 468 negatives; an independent scan verifies that every uncovered pair has a surviving witness. This establishes the numerical certificate for five omissions, with the Lean certificate and the general three-free-gate structure still to prove.

**PlaneCase35NinthTraceBound — ACCEPTED (check), exit 0**, 2,131 rechecked constants, one research module and 87 upstream definition modules in the matched manifest. The axiom list is propext, Quot.sound, Classical.choice. The expanded statement and independent pinned leanchecker replay also passed. The first build caught two transcription errors in a cardinality helper and the quantified wire order; both were fixed in the accepted source. Thirteen threshold-dispatch regression cases passed, including other ninth gates and reversed orders. Prepared one-file comparison: https://github.com/seankim96/pequalnp-proofs/compare/982e0733951c7f572dbc695fc4a38e4ca8408222...9bb5fb324671c495ae14552950e4a530d73aa5e7 .
