# L-meta-2625 — sparse positive support after code 975

Parent 2364c9d2375f2ad731c0b87f4a280990d1f8c4fd. The restored checkout matches both fork sources Plane888SingleDeletion and Plane888AllFifthAnd byte for byte. The previous run's lost checker verdict could not be recovered. The previously accepted coverage at fourth code 888 is 775 of 900 immediate fifth AND codes.

Case 6 has gates AND(0,13), OR(0,14), AND(1,13), AND(1,18); fifth code 975 adds AND(2,15). All 52 positive and 468 negative rows are used. The desk reports one other active holder, since 02:45:45Z. This run took no lease and filed no upstream PR. PRs #7762 and #8170 are merged.

## New mask and finite sixth-gate count

Mask 0x10100001103f3 admits a shared family of 257 negatives. For each pair a retained positive is covered by the union of its two 31-wire row words. Plane975Mask extends this certificate through an arbitrary OR list before an AND whose positive support lies inside the mask. Its claim is nine ANDs strictly after that AND. Plane975SixthAndCodes specializes it to 857 of the 961 ordered immediate sixth ANDs. The first version built with Lean 4.36.0; the checker reported CHECKER FAULT, verifier exit 137. A smaller column-lookup proof is being checked separately. This is restricted lower-bound work; 63 unrestricted gates remain open.

## Multiple intermediate ANDs

PlaneSparseAndPrefix uses a single flag set shared by an entire intermediate gate list. On positives outside the set every intermediate AND is false. OR gates preserve each pair witness. If deleting at most 211 of the 468 negatives leaves witnesses outside the flag set for every pair, at least 257 negatives remain, giving at least nine AND gates in the final suffix. The intermediate list has no length limit. The theorem does not assert that an arbitrary AND gate has small support.

For each pair store the mask of all positives it covers. Deleting a flag set S destroys exactly the pairs whose witness mask is a subset of S. Removing all higher endpoints or all lower endpoints of destroyed pairs gives two independent families. Keep the larger. The script enumerates deletion sets by size and directly checks the two endpoint sets on a worst example per size. For all 270,725 four-flag sets the worst smaller endpoint count is 144 in code 888 and 162 in code 975. Thus at least 324 and 306 negatives remain respectively. These are finite-computation results, not a closed Lean certificate for all flag sets.

Source and statement files record the new proofs. Use research/order3_sparse_and_prefix.py for the numerical enumeration.
