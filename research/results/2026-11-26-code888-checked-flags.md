# L-meta-2625, case 6, code 888

Parent e5d0900f03fd0ae45a4b99a5755ede015a798d86. The fixed physical gates are AND(0,13), OR(0,14), AND(1,13), AND(1,18). All 52 positive and 468 negative input tests are used.

Plane888NineFlags checks all 32,896 pairs of 257 selected negatives against the original words. Whenever the first further AND after an arbitrary OR prefix is positive only on flags in 0x1604e3, at least nine more AND gates must follow it. Both constant wires, arbitrary sharing and arbitrary output choice are allowed. The previous candidate used reserved identifiers; the compiled version uses omittedFlags and firstAnd.

Plane888ThreeRepresentatives applies that certificate to the three representatives {2,4,10} / {1,14}, {14,17} / {4,16}, and {15,17} / {4,5}. Each operand may be positive on any subset of its raw disjunction's positive support enlarged by wires 26, 28 and 29. Negative operand values are unrestricted. The earlier numerical transport to all 40 syntaxes and coverage of the remaining 35,538 orbits still require their concrete Lean links.

Plane888FifthAndCodes proves the count and bound together. For 775 of the 900 ordered immediate fifth AND gates, at least nine AND gates remain after that gate. The 775 include 732 zero-positive columns and 43 nonzero codes. Thus those branches require at least ten AND gates after gate four including the fifth gate. The unrestricted 63-gate question remains open.

## Bounded search

CaDiCaL 2.1.2, 120 seconds, 63 gates total. After code 888, fix fifth code 974, AND(2,14). The suffix has 58 slots, at least 9 AND and 18 OR. Two positive and two negative rows seed the encoding. Candidates were checked against all 520 rows. UNKNOWN at timeout, with 32 rows encoded and eight rejected candidates. Reproduce with research/order3_prefix_search.py --case 6 --third AND 1 13 --fourth AND 1 18 --fifth AND 2 14 --operator-bounds --seconds 120 and the pinned cadical binary. Five encoder checks exercised the original four-gate path, covered and uncovered fifth AND, fifth OR, and a different fourth gate.

The three concrete circuit lemmas built with Lean 4.36.0. The earlier JavaScript orbit verifier was rerun on the parent data. The project desk reported another active holder of L-meta-2625. This session took no lease and filed no upstream PR. PRs #7762 and #8170 were merged with accepted upstream checker reports and no pending review requests.

PlaneMatchingAndBudget formalizes the counting argument for the other orbit classes. Given a finite match function with a base positive witness for each nonexcluded negative pair, remove the higher endpoint of every internal conflicting edge. If 257 vertices remain in either orientation where one operand implies the other, the first AND leaves nine more AND gates necessary. This is a general conditional reduction. The code-888 matching table and its finite side counts still have to be connected.

The first standalone checker for Plane888NineFlags ended with CHECKER FAULT (verifier exit 137); that run supplied no verdict. A serialized retry is tracked separately.


## Smaller certificate and pinned project checker

The original explicit-pair version built in 443 seconds. Its standalone checker retry ended with CHECKER FAULT (verifier exit 137). The checker processes for the three representatives and the fifth-gate count also exited 137 without verdicts. These events concern verification resources, not satisfiability.

The revised Plane888NineFlags proves the same statement with 26 bitsets. Bit j in a bitset names one of the 257 selected negatives. For each wire, the proof checks that every named negative contains the wire's stored common bits. For each source row i and wire it can use, a packed entry gives a retained positive covered by row i together with those common bits. The union of the usable bitsets covers every other selected negative. This certifies all 32,896 unordered pairs using 2,302 row/wire entries, six to fourteen per row. To regenerate the packed choices, consider the wires in ascending order, associate the first eligible positive to each wire, and greedily choose the wire covering the most still-uncovered negatives, breaking ties by wire index. Encode unused entries as 63. The data and the implication are both checked in Lean.

PlaneMatchingAndBudget: ACCEPTED (check), exit 0. The kernel rechecked 1,705 constants. Source hashes matched all three research modules and all 86 definitions modules in the checker manifest.

The smaller Plane888NineFlags built in 47 seconds and the unchanged project checker returned ACCEPTED (check), exit 0, rechecking 1,893 constants against the expanded statement. Only propext, Classical.choice and Quot.sound were reported.

## Handoff for the other 125 immediate AND codes

Run `python research/order3_code888_residual.py`. A scalar comparison on all 520 rows shows that 31 of the other 125 ordered AND codes duplicate an existing column. Replaying them as a free OR of that column with itself should preserve the prior nine-AND suffix bound. Each of the remaining 94 codes is true on a single positive; they use 43 distinct positive flags. For these codes two negative families suffice. In each family, after deletion of any one of its flagged positives, all selected negative pairs retain a positive witness. The script independently rechecks 32,896 pairs per family, 65,792 in total, against the original words. These identities and the two finite certificates are numerical results. To finish the 900-code lemma, formalize duplicate-wire replay and a retained-witness argument allowing one deletion per family.

| Single-deletion flag group | Negatives found (257 used) | Flags | Residual ordered AND codes |
| --- | ---: | ---: | ---: |
| 0xf5048ff40f800 | 261 | 22 | 46 |
| 0xafb700a9031c | 259 | 21 | 48 |

Plane888FifthAndCodes: ACCEPTED (check), exit 0, 1,903 constants rechecked. This verdict covers the count of 775 and the bound of nine further AND gates for each of those codes.

Plane888ThreeRepresentatives: ACCEPTED (check), exit 0, 1,898 constants rechecked. This covers the three named representatives under their positive-support assumptions. The symmetry transport to 40 syntaxes remains numerical.

All four final checker manifests matched the judged sources. All research-module hashes also matched the fork sources. Each verdict listed only propext, Quot.sound, and Classical.choice. The assignment still had one other desk holder at the final check.
