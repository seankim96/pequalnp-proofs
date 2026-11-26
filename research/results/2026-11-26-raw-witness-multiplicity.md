# L-meta-2625 — raw input pairs and residual sixth ANDs

Parent 05e35ea1551986685edb483514104f141e2449e8. The project desk marked the gap leased to another session since 09:13:36Z. No lease was acquired, renewed or released by this session. Upstream main still has three reductions and no final L_meta_2625 file. PRs #7762 and #8170 are merged. No upstream PR.

Code 975 fixes AND(0,13), OR(0,14), AND(1,13), AND(1,18), AND(2,15). For residual family 2 (mask 0x20002f080400), Plane975Family2Codes: ACCEPTED (check) under the pinned Lean 4.36.0 toolchain. The kernel rechecked 2,012 constants with only the permitted axioms, and all four research module and 86 definition hashes matched disk. The statement enumerates exactly 18 new ordered sixth-AND codes from the residual JSON, and proves that any following circuit separating all 52 positives from all 468 negatives requires at least nine further ANDs. Coverage advances from 875 to 893 of 961.

## Raw-input multiplicities

Use the original 26 input wires. For each negative pair {a,b} let W(a,b) be the set of positive tests bitwise contained in a OR b. After discarding positive flags S, this pair loses all witnesses exactly when W(a,b) is contained in S. No raw pair has an empty witness set. Over the 109,278 pairs, the maximum number with the same exact witness mask of size 1,2,3,4,5 is respectively 18,4,3,2,1. This histogram is computed.

PlaneFiveFlagMultiplicity: ACCEPTED (check), 1,662 kernel constants, one research source and 86 definitions hashes verified. Under those five endpoint multiplicity bounds and zero empty-mask endpoints, any at-most-five-flag subset excludes at most 171 higher endpoints. Its proof bounds layers by C(5,k) times the respective multiplicity, leaving at least 297 negatives. The abstract counting theorem is kernel checked. The concrete premise about all original pairs is still numerical.

## Exhaustive deletion test

Compile research/plane_raw_deletion_scan.cpp with a C++20 compiler and -O3. Pass the binary path to python research/plane_raw_deletion.py. No SAT solver or symmetry reduction is used. Both enumeration cardinalities and the aggregate number of failed pairs are checked against binomial identities. The maximizing example at each size is checked separately using the 520 raw input words. Ordered input swaps are not counted twice in the pair histograms.

| Deleted flags | Sets tested | Maximum failed pairs | Sets exceeding 211 | Guaranteed remaining negatives |
|---|---:|---:|---:|---:|
| 5 | 2,598,960 | 138 | 0 | 330 |
| 6 | 20,358,520 | 177 | 0 | 291 |
| 7 | 133,784,560 | 228 | 45,864 | 257 |

For at most 211 failed pairs, discard one endpoint per pair. For each of the 45,864 exceptional seven-flag sets the replay checked every submask, reconfirmed the pair count, then retained the larger of the families obtained by removing all low or all high endpoints. The worst loss on these exceptional sets was only 141 endpoints. The 257 bound over all seven-flag sets is conservative. By extending smaller deletions to seven, the guarantee covers every size up to seven. Applying the already checked PlaneSparseAndPrefix lemma gives a numerical certificate for at least nine ANDs strictly after any prefix of the raw inputs in which every AND is true only on a common set of at most seven positive tests. There is no bound on the number of intervening OR gates. These constraints on the ANDs are essential.

## Symmetry compression for the remaining numerical premise

The three checked-in stage-0 wire permutations act on all 52 flags and all 468 negative tests. The orbit replay verified they are permutations of both lists, that the negatives form one orbit, and that every computed witness mask transforms into its predicted class. The 109,278 unordered negative pairs form 27 orbits and their exact masks form 25 orbits. Only six witness-mask orbits have size of mask at most five. Listed as (mask representative, mask orbit size, unordered pairs, multiplicity per mask, partners of negative row 0):

- 0x1, 52, 936, 18, 4
- 0x21, 702, 2808, 4, 12
- 0x2102, 468, 1404, 3, 6
- 0x65, 1404, 2808, 2, 12
- 0x161, 5616, 5616, 1, 24
- 0x24c1, 5616, 5616, 1, 24

In each orbit, 468 times the last count equals twice its unordered pair total. These are direct Python checks. They suggest a smaller way to formalize the multiplicity premise by generating the mask orbits and checking the 467 partners of one negative row. Reproduce with python research/plane_raw_pair_orbits.py.

SAT probe: fixed sixth AND code 81 = AND(2,19), 63 total gates, 57 remaining slots, no additional gate-count pruning. Initial rows were all 52 positives plus negative indices 0 and 234. CaDiCaL 2.1.2 used a 60-second wall-clock budget, 16,131 variables, 560,364 clauses, 54 encoded rows, zero decoded candidates. Verdict UNKNOWN (timeout).

PlaneFiveFlagSuffixBudget: ACCEPTED (check), exit 0, 1,711 kernel constants using only propext, Classical.choice and Quot.sound. Five research-source hashes and 86 definition hashes matched disk. This formally connects the five endpoint multiplicities to the nine-AND suffix lower bound for any prefix whose AND gates are true only on the same set of at most five positives. It uses the upper endpoint of each failed pair. Its finite multiplicity hypothesis still requires a concrete proof for the raw 26-wire plane.

Prepared two further lemmas for the symmetry argument. Both compiled with pinned Lean before repository-checker replay. PlaneRawNegativeOrbit gives an explicit word of stage-0 pull permutations taking negative row zero to every negative row (breadth-first witness table, maximum depth nine). PlaneRawAnchorCensus directly enumerates the 467 remaining partners of row zero. Its tally packs counts in nine-bit fields. Field 0 counts empty masks; fields 1–3 count masks of those sizes; fields 4 and 5 split four flags by whether the smaller number of distinct points and lines equals two; field 6 counts five flags; field 7 counts all larger masks. Counts are 0,4,12,6,12,24,24,385. These two claims do not by themselves establish all mask-orbit sizes or fiber multiplicities. Final checker verdicts follow when available.

## Third residual family

Plane975Family3Codes was ACCEPTED (check), 2,012 kernel constants, permitted axioms only. All four research-source and 86 definitions hashes matched. Mask 0x40f000f00000 covers 18 further ordered sixth ANDs, disjoint from all preceding lists. The two new families together advance the checked restricted count from 875 to 911 of 961. Fifty remain, recorded in the residual JSON. The next family begins with mask 0xf000080f (14 cases). A later desk check showed resting_after_expiry for the other session's lease. No lease action was taken.

For a route to a concrete multiplicity proof, one can avoid proving all orbit cardinalities by transporting both negative rows. First transport the first negative to row zero, then map its anchored witness mask to one of the six small representatives. For each representative directly count the negative pairs with that exact mask. A separate bit-parallel replay intersected, for each first negative and each flag, the 468-bit set of second negatives supplying its missing raw wires (or its complement for an absent flag). It independently reproduced 0,18,4,3,2,1,1 pairs for the empty mask and the six representatives. Transport of the small anchored masks and formal multiplicity replay remain future work.

## Kernel checks on the anchored reduction

PlaneRawAnchorCensus: ACCEPTED (check), 1,665 constants, only propext. PlaneRawNegativeOrbit: ACCEPTED (check), 1,742 constants, propext and Quot.sound. Each had one research source and 86 definition hashes verified against disk. The initial single-batch row-orbit kernel replay ended without verdict (exit 137); dividing the 468 edge checks into blocks of eight allowed the same statement to pass. The constructive row-orbit theorem and the anchor census are now kernel checked, not just compiled.
