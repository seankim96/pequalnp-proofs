# L-meta-2625, case 6, code 888

Parent e5d0900f03fd0ae45a4b99a5755ede015a798d86. The fixed physical gates are AND(0,13), OR(0,14), AND(1,13), AND(1,18). All 52 positive and 468 negative input tests are used.

Plane888NineFlags checks all 32,896 pairs of 257 selected negatives against the original words. Whenever the first further AND after an arbitrary OR prefix is positive only on flags in 0x1604e3, at least nine more AND gates must follow it. Both constant wires, arbitrary sharing and arbitrary output choice are allowed. The previous candidate used reserved identifiers; the compiled version uses omittedFlags and firstAnd.

Plane888ThreeRepresentatives applies that certificate to the three representatives {2,4,10} / {1,14}, {14,17} / {4,16}, and {15,17} / {4,5}. Each operand may be positive on any subset of its raw disjunction's positive support enlarged by wires 26, 28 and 29. Negative operand values are unrestricted. The earlier numerical transport to all 40 syntaxes and coverage of the remaining 35,538 orbits still require their concrete Lean links.

Plane888FifthAndCodes proves the count and bound together. For 775 of the 900 ordered immediate fifth AND gates, at least nine AND gates remain after that gate. The 775 include 732 zero-positive columns and 43 nonzero codes. Thus those branches require at least ten AND gates after gate four including the fifth gate. The unrestricted 63-gate question remains open.

## Bounded search

CaDiCaL 2.1.2, 120 seconds, 63 gates total. After code 888, fix fifth code 974, AND(2,14). The suffix has 58 slots, at least 9 AND and 18 OR. Two positive and two negative rows seed the encoding. Candidates were checked against all 520 rows. UNKNOWN at timeout, with 32 rows encoded and eight rejected candidates. Reproduce with research/order3_prefix_search.py --case 6 --third AND 1 13 --fourth AND 1 18 --fifth AND 2 14 --operator-bounds --seconds 120 and the pinned cadical binary. Five encoder checks exercised the original four-gate path, covered and uncovered fifth AND, fifth OR, and a different fourth gate.

All three new circuit lemmas built with Lean 4.36.0. The earlier JavaScript orbit verifier was rerun on the parent data. The project desk reported another active holder of L-meta-2625. This session took no lease and filed no upstream PR. PRs #7762 and #8170 were merged with accepted upstream checker reports and no pending review requests.

PlaneMatchingAndBudget formalizes the counting argument for the other orbit classes. Given a finite match function with a base positive witness for each nonexcluded negative pair, remove the higher endpoint of every internal conflicting edge. If 257 vertices remain in either orientation where one operand implies the other, the first AND leaves nine more AND gates necessary. This is a general conditional reduction. The code-888 matching table and its finite side counts still have to be connected.

The first standalone checker for Plane888NineFlags ended with CHECKER FAULT (verifier exit 137); that run supplied no verdict. A serialized retry is tracked separately.
