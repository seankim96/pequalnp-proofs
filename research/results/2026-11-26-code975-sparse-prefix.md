# L-meta-2625 — sparse positive support after code 975

Parent 2364c9d2375f2ad731c0b87f4a280990d1f8c4fd. The restored checkout matches both fork sources Plane888SingleDeletion and Plane888AllFifthAnd byte for byte. The previous run's lost checker verdict could not be recovered. The previously accepted coverage at fourth code 888 is 775 of 900 immediate fifth AND codes.

Case 6 has gates AND(0,13), OR(0,14), AND(1,13), AND(1,18); fifth code 975 adds AND(2,15). All 52 positive and 468 negative rows are used. The desk reports one other active holder, since 02:45:45Z. This run took no lease and filed no upstream PR. PRs #7762 and #8170 are merged.

## New mask and finite sixth-gate count

Mask 0x10100001103f3 admits a shared family of 257 negatives. For each pair a retained positive is covered by the union of its two 31-wire row words. Plane975Mask extends this certificate through an arbitrary OR list before an AND whose positive support lies inside the mask. Its claim is nine ANDs strictly after that AND. Plane975SixthAndCodes specializes it to 857 of the 961 ordered immediate sixth ANDs. The first version built with Lean 4.36.0; the checker reported CHECKER FAULT, verifier exit 137. A smaller column-lookup proof is being checked separately. This is restricted lower-bound work; 63 unrestricted gates remain open.

## Multiple intermediate ANDs

PlaneSparseAndPrefix uses a single flag set shared by an entire intermediate gate list. On positives outside the set every intermediate AND is false. OR gates preserve each pair witness. If deleting at most 211 of the 468 negatives leaves witnesses outside the flag set for every pair, at least 257 negatives remain, giving at least nine AND gates in the final suffix. The intermediate list has no length limit. The theorem does not assert that an arbitrary AND gate has small support.

For each pair store the mask of all positives it covers. Deleting a flag set S destroys exactly the pairs whose witness mask is a subset of S. Removing all higher endpoints or all lower endpoints of destroyed pairs gives two independent families. Keep the larger. The script enumerates deletion sets by size and directly checks the two endpoint sets on a worst example per size. For all 270,725 four-flag sets the worst smaller endpoint count is 144 in code 888 and 162 in code 975. Thus at least 324 and 306 negatives remain respectively. These are finite-computation results, not a closed Lean certificate for all flag sets.

Source and statement files record the new proofs. Use research/order3_sparse_and_prefix.py for the numerical enumeration.

## Checked general theorem and five-flag results

PlaneSparseAndPrefix: ACCEPTED (check), exit 0 on pinned Lean 4.36.0. The checker rechecked 1,706 constants and reported only propext, Quot.sound and Classical.choice. All three research source hashes and 86 definitions hashes matched. The first draft had a reserved identifier and a let-binder elaboration error; both were corrected before this verdict.

The numerical scan ran all 2,598,960 five-flag sets independently at each prefix. The maximum number excluded by choosing the better of the high and low endpoint sets was 162 at code 888 (flags 2,3,5,6,7), and 184 at code 975 (flags 3,10,11,22,23). Thus 306 and 284 negatives respectively survive in the worst cases. Every smaller size 1–4 was separately exhausted. The scalar replay independently recomputed both endpoint sets on each worst example. These finite premises were checked by Python, not by the general Lean theorem.

## Code 975 SAT replay and conjunctions

The unchanged SAT driver, CaDiCaL 2.1.2, 63 total gates and 58 suffix slots, at least 8 AND and 18 OR, --all-positives --operator-bounds --seconds 90: UNKNOWN at the 90-second limit, 54 rows encoded (52 positive, two negative), zero decoded candidates. No unrestricted verdict follows.

Plane975AndConjunction built with Lean 4.36.0. Its conclusion holds for nonempty conjunctions of arbitrary length from the 31 available wires. Either the result agrees with a single existing wire on every raw input word or it can be true on at most one of the 52 positive test rows. The proof classifies the 31 × 31 physical pairs using positive masks and then inducts on conjunction length. This is stronger in scope than a test of just the immediate sixth AND. The replay of the finite meet closure independently found 9,339 distinct signatures on all 520 rows, including 9,252 non-base signatures with zero positive support and 56 with singleton support. The smallest conjunction lengths 1 through 6 first produced 31, 346, 1,492, 3,654, 2,880 and 936 signatures. The exact closure counts are numerical. Replacing a duplicate AND by the OR of the original wire with itself preserves its signal, so a run of at most five ANDs after code 975 exposes at most five new positive flags after those replacements. The five-flag premise above remains numerical.

Plane975AndConjunction: ACCEPTED (check), exit 0, 1,801 constants rechecked on pinned Lean 4.36.0. All 86 definition hashes and its sole research-module hash matched. The unrestricted length here is the length of an AND-only conjunction, and disagreement between the two alternatives is not required. This is a verified structural reduction for code 975, including all 961 immediate sixth AND operand pairs.
