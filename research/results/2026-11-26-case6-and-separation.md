# L-meta-2625 — separating negative pairs in case 6

Parent checkpoint c0b4a7bb82ba7407c90db0904f0e41f886a38deb. Wires 26, 27, 28 and 29 are AND(0,13), OR(0,14), AND(1,13) and OR(2,26), respectively. The new fourth gate is code 84. The target has 52 positive and 468 negative test rows. There are 59 free gate slots in the bounded search. The proofs allow arbitrary suffix length, reuse of previous wires, arbitrary output and both constants.

## Lower bound

On a negative row, record the left input bit at each AND gate in the suffix. A suffix with k AND gates has at most 2^k such records. If two negatives have the same record and their bitwise union contains a positive input row, then every wire accepting that positive accepts at least one of the two negatives. This is immediate for input wires and propagates through OR. At an AND, either both negative left bits are false, contradicting acceptance of the positive on the left, or both are true, in which case the right input supplies a negative accepted by the AND. Thus one output accepting every positive and rejecting all the selected negatives must assign distinct records to them. 257 negatives force at least nine suffix AND gates.

PlanePairAndCount proves the argument for arbitrary 32-bit input rows. PlaneCode84AndCount identifies 257 distinct negative rows among the actual 468, checks all 32,896 unordered pairs against the positive rows, and checks the packed input rows against the actual prefix columns including constants. Its target states the result directly on the full 520 tests. Together with the earlier 18-OR result, at least 27 of the 59 suffix slots are required. The unrestricted 63-gate existence question remains open.

## Reproduction and scope

Run `python research/order3_and_pair_certificates.py` to scan every ordered fourth gate after the first three fixed gates. On 1,682 codes (775 distinct signatures), greedy selection returns 414 to 432 negatives with the pair property. The first minimum is code 858; code 84 returns 432. The scan independently verifies the pairs for those two codes using the actual positive and negative row masks. Only the 257-row certificate for code 84 is instantiated in the branch-specific Lean theorem. A natural next step is to formalize a common family of certificates for the other codes, starting with 858.

The two SAT runs use case 6, third AND 1 13, fourth OR 2 26, the four-row seed, 63 gates and all 520 tests for counterexample refinement. CaDiCaL 2.1.2 comes with the repository-pinned Lean 4.36.0 distribution. The prior checkpoint's --operator-bounds requires at least 2 AND and 18 OR in the suffix. This checkpoint strengthens that option only for code 84 to at least 9 AND and 18 OR. A timeout leaves the verdict UNKNOWN.

| Free AND minimum | Free OR minimum | Solver budget | Final encoded rows | Rejected candidates | Verdict |
| ---: | ---: | ---: | ---: | ---: | --- |
| 2 | 18 | 120 s | 38 | 9 | UNKNOWN |
| 9 | 18 | 180 s | 40 | 9 | UNKNOWN |

The two decoded-candidate counts are per run. No disjointness is asserted. The desk reported one existing holder; no lease was taken, renewed or released by this session. Prior PRs #7762 and #8170 are merged with accepted checker comments.

Both statements passed tools/check-lean.mjs in check mode under Lean 4.36.0 (exit 0). The kernel rechecked 1,699 constants for PlanePairAndCount and 1,970 for PlaneCode84AndCount, with only propext, Classical.choice and Quot.sound listed.
