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
