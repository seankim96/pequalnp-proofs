# L-meta-2625 — nine AND gates strictly after gate five

Parent research head: 61927a1fe6a41ebff0036a7c579adddb3ff9429a. Upstream verification base: 553c12384affd9e643073c31ee278f732dea28b7. Toolchain: leanprover/lean4:v4.36.0.

## The theorem

The fixed prefix is OR(0,1), OR(3,9), AND(15,27), AND(17,26). The fifth gate can be either operator, with any ordered pair of the 30 preceding wires. Equal operands and reused wires are allowed. The free suffix can read the resulting pool plus constant false and true, has arbitrary length, and may select any output wire. Any suffix agreeing with the 52 positive and 468 negative tests contains at least **nine AND gates**. This includes all 1,800 choices at gate five. In particular, the 900 fifth-AND choices improve from eight to nine remaining ANDs. For those choices the previous nineteen-OR bound after gate four still requires all nineteen ORs in the suffix. A circuit with such a prefix needs at least 5 + 9 + 19 = 33 gates, versus 32 from the preceding checkpoint.

For the trace argument, each pair in a family of 257 negative rows must share an accepted positive whose active starting wires also activate on at least one member of the pair. The separation condition forces distinct AND traces on all 257 negatives. Eight AND gates give at most 256 traces. The earlier PlaneFirstAndBudget supplies the trace theorem. This session constructs the necessary families after the fifth gate, including the cases where its inputs span a third projective line.

- For a fifth OR, any positive it accepts is inherited from one of its operands.
- For a fifth AND, PlaneCase35FifthAndShape proves that either its column equals a parent, at most one positive is accepted, or its accepted positives lie in {0,1} or {2,3}. Equality with a parent is proved on every natural row index. Among the 900 ANDs there are 46 parent equalities. The rest accept zero, one or two positives in 718, 132 and four cases respectively (counts from replay).
- The two preceding ANDs are active only on positive flags 9 and 16. For a singleton fifth exception u the certificate therefore avoids flags 9, 16 and u. For the two double-exception types a seed family avoids flags 0–3, 9 and 16 simultaneously.

The modular proof uses masks 0x103ff and 0xf000f10200. The first yields 260 negatives by the deterministic selection rule, of which the first 257 are used. Seventeen images of its mask cover all singleton cases except flags 20–23 and 36–39. The second seed covers these eight cases and yields 278 negatives. The transport proof checks the permutations, coverage of their pair images and selection for each of the 52 flags. Direct finite replay also checks all 32,896 pairs in each of the 18 selected families.

PlaneCase35FifthDirect is a separate one-file proof importing only Mathlib. A different seed, 0x4020141020f, omits flags 0,1,2,3,9,16,22,24,33,42. It yields 302 negatives. Sixteen images of its 257-row subfamily cover every singleton case, with the untransformed seed also handling the two double exceptions. This version incorporates the AND trace proof and classification. Both complete versions have the same expanded statement.

## Verification

The project checker accepted the following independently checked statements; each check exited 0. Manifest digests matched the committed research sources and the 87 definition modules at the verification base.

| File | Checked statement | Kernel constants |
|---|---|---:|
| PlaneCase35FifthAndShape | all ordered fifth ANDs have the stated parent-or-small-support classification | 1,750 |
| PlaneCase35FifthGuard | a 257-negative family avoiding the 11-flag first mask | 2,053 |
| PlaneCase35SecondFamily | a 257-negative family avoiding the second mask | 2,045 |
| PlaneCase35FifthTransport | the two seed families imply avoidance of 9, 16 and any specified singleton | 2,150 |
| PlaneCase35FifthComposition | the singleton and four-flag family conditions imply the nine-AND budget | 1,879 |

PlaneCase35EveryFifthAndBudget supplies the premises to the checked composition theorem. Its build, type check against the expanded statement and pinned leanchecker replay each exited 0. The combined project verifier returned FAULT (exit 137) while replaying the assembled module. An earlier combined guard-and-eligibility implementation also reached exit 137; extracting the seed-family statement produced the accepted PlaneCase35FifthGuard above. All accepted axiom lists contained only propext, Quot.sound and Classical.choice.

**PlaneCase35FifthDirect: ACCEPTED (check), exit 0.** The pinned project checker rechecked 2,440 kernel constants on the complete one-file theorem. The manifest contains only that one research source (SHA-256 1f748333f70180e6ffb16420c3b9c8f408140251dbcd48c2f3dda0fbbfd7315f) and 87 upstream definition modules. The theorem also type-checked against the expanded statement and passed a separate pinned leanchecker replay, both exit 0. An earlier one-file version put all the mask transports into one proof and its checker process was killed (exit 137). In the accepted file each transport edge is a separate declaration. This is project-checker acceptance for the stated five-gate-prefix lower bound on the fork.

Use the pinned toolchain from the fork root, substituting each theorem name:

    node tools/check-lean.mjs lean/PEqualNP/Research/<name>.lean research/statements/<name>.txt check
    python3 research/order3_case35_fifth_guard.py

## 63-gate experiment

Case 35, fifth AND(13,26), accepts exactly flags 0 and 1. The 58 free binary gates were constrained to at least nine ANDs and nineteen ORs. CaDiCaL 2.1.2, 90-second wall budget for solving and refinement, starting with all 52 positives and negative indices 0 and 234. The initial CNF had 17,980 variables and 573,328 clauses. Verdict **UNKNOWN**, 54 encoded rows, zero decoded candidates. The bounded search returned neither a witness nor an impossibility certificate. The search uses 26 raw inputs; the more permissive constants in the Lean theorem preserve its applicability. Threshold dispatch was checked on the new fifth AND, a fifth OR, and a different four-gate prefix.

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --operator-bounds --all-positives --seconds 90 --solver /path/to/cadical

## Gate six — numerical follow-up

    python3 research/order3_case35_sixth_and_exceptions.py

For each new wire, keep the positives it accepts without a preceding wire that is active there and is contained in it on every test row. The fifth and sixth exceptional sets together have sizes 0, 1, 2, 3 and 4 for 2,971,444, 455,960, 31,136, 1,048 and 12 ordered gate extensions, respectively. These total 3,459,600 with 1,480 distinct masks. Using the actual 30 wires before gate five, the respective maximum numbers of distinct higher negative endpoints for an exact witness mask of size 0–4 are 24, 24, 6, 3 and 4. Consequently any four excluded flags discard at most 172 endpoints by the binomial sum. For the 1,480 masks actually encountered, the largest union discards only 96, leaving at least 372 negatives. This is finite Python evidence toward nine ANDs strictly after gate six, with no such general Lean theorem in this commit. The all-sixth bound is the next open case. A route to a short structural proof of the four-flag cap uses distributivity. A fifth OR followed by an AND reading it and an old wire expands to a disjunction of two ANDs of old wires. Each such AND either inherits a parent or contributes at most two positive flags, by the checked fifth-gate shape theorem. A fifth AND confined to two flags remains confined to them under another AND reading it. If the sixth AND uses two old wires it contributes at most two additional flags. An OR inherits cover witnesses from each parent. The outstanding large finite lemma is the endpoint multiplicity bound on the actual 30-wire rows.

## Project status

The desk returned not_open for L-meta-2625. The upstream tree contains the three reductions R_meta_2625_317, _487 and _50. No resolution of the unrestricted 63-gate question was identified. The five prepared L-meta branches were listed. All four existing upstream PRs by seankim96 are closed. #7762 and #8170 are merged, have ACCEPTED intake comments, and have no reviews, review requests or inline comments requiring a change. No standard lease was acquired, renewed or released. The branch-specific statements are published on the research fork; no upstream PR was opened.
