# L-meta-2625: all immediate fifth AND operands after fourth code 888

Parent 50c8b89861dbf1b75e0ef85ffa823880ba4b1c6d. The physical prefix is AND(0,13), OR(0,14), AND(1,13), AND(1,18). Rows are the 52 positives and 468 negatives of the order-three instance. An immediate fifth AND picks an ordered pair from the 30 earlier physical wires, giving 900 choices. The suffix is arbitrary and may share wires. Both Boolean constants are available in the formalization.

## Lean results and verification status

Plane888SingleDeletion uses two families of 257 negatives. In a family, a negative pair either covers a positive outside that family's deletion mask or covers at least two different positives. Either condition supplies a witness after any one flag in the mask is removed. The masks provide 22 and 21 distinct flags. The packed certificates were independently regenerated from the original rows and their covering identities passed for all 514 source rows. The two groups cover the 94 residual singleton AND codes.

Plane888AllFifthAnd combines this lemma with the parent's accepted 775-case result. For the other 31 cases the two operands coincide or one is 0 or 14 paired with wire 27, their disjunction. The AND therefore reproduces a starting wire on every test. The conclusion for all 900 choices is at least nine AND gates strictly after the fifth gate, or ten after the fourth including the fifth. This is a restricted gate-count lower bound. It leaves the unrestricted 63-gate question open.

Both theorem modules compiled with pinned Lean 4.36.0. The project checker built Plane888AllFifthAnd and its definitions root and started kernel replay. The first full run produced CHECKER FAULT (verifier exit 137). The separate single-deletion run also terminated with 137 without a verdict. A standalone retry of the 900-case checker reached verifier reading, then the executor disconnected before its verdict could be retrieved. No new ACCEPTED verdict was observed. The sources and expanded statements were reconstructed from the run's inputs after the disconnect; a byte comparison with the disconnected checkout was unavailable. Keep the SAT driver's previously accepted coverage on the research branch until a completed replay. Run each project checker in isolation, with no simultaneous solver or other Lean build. If memory remains limiting, split the finite checks further; the 257-bit certificates themselves require no solver.

## One unfinished 63-gate SAT case

Case 6, fifth full code 975, AND(2,15), single positive flag 8. There are 58 suffix slots. With at least 8 AND and 18 OR, CaDiCaL 2.1.2 reached its 120-second limit: UNKNOWN, 36 active rows and 10 rejected candidates. Initial rows: two positive and two negative. Candidate checking uses the full 520 rows. Reproduce with research/order3_prefix_search.py --case 6 --third AND 1 13 --fourth AND 1 18 --fifth AND 2 15 --operator-bounds --seconds 120 and the pinned cadical binary. An experimental 9-AND/18-OR run with the same budget was killed (signal 9) before a solver verdict. It was not an UNSAT result or an observed timeout.

The project desk still reported another holder of L-meta-2625 (since 02:45:45Z). This run acquired, renewed and released no standard lease. PRs 7762 and 8170 are merged and their review-thread lists were empty. No upstream PR was opened.
