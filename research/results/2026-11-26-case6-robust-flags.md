# L-meta-2625 — the 117 remaining fourth-gate cases

Parent d3749d449186addb4c0337e8b4b56b90a998e5d8. Case 6 starts with AND(0,13), OR(0,14), AND(1,13). A fourth-gate code below 841 denotes OR; 841 + 29a + b denotes AND(a,b). Counts below include both operand orders. The target has 52 positive and 468 negative tests. Every suffix theorem allows sharing, arbitrary length and output wire, and both constants.

## Cover

The previous run certified at least nine suffix AND gates for 1,565 codes and eight for the other 117. Of these 117, an ideal fourth wire with positive support 0x10001010121f and no negative support covers 24 additional codes. Thirty-one of the 117 have a fourth-wire column identical on all 520 rows to that of an OR code. Equality of the entire initial state gives equal outputs for every suffix and output. Ten of the 31 overlap the new mask. After these steps, 72 ordered codes remain, with 36 distinct fourth-wire signatures.

Each remaining fourth wire is true on exactly one positive flag. To prove a lower bound after granting it, omit the exceptional positive from the separating-pair argument. The fourth wire is now false on every retained positive. On negatives, replacing it by false can only decrease a monotone circuit output. Correctness on the retained positives and all negatives survives.

Two negative families handle the 36 possible omitted flags. For every pair of negatives in a family, the union covers either a positive outside the family's omission set or two distinct positives. At least one witness therefore survives whichever flag is omitted. Choose 257 negatives, requiring 257 distinct records of the left input bit at suffix AND gates. Eight bits provide at most 256 records.

| Family | Omission mask | Omissible flags | Greedy negative set | Used | Ordered codes |
| --- | --- | ---: | ---: | ---: | ---: |
| A | 0xa240d46448500 | 15 | 294 | 257 | 30 |
| B | 0x4caf2a9aa6800 | 21 | 265 | 257 | 42 |

The disjoint allocation of all fourth codes is 841 OR, 724 original-mask AND, 24 additional-mask AND, 21 additional OR-equivalent AND, 30 family-A AND and 42 family-B AND. The robust witness construction can be replayed with python research/order3_robust_flag_families.py. It independently enumerates all 32,896 pairs in each family and checks the omission property.

## Bounded search

Code 888 is AND(1,18), preceded by the three fixed gates above. For a total budget of 63 gates the suffix has 59 slots. Run research/order3_prefix_search.py with --case 6 --third AND 1 13 --fourth AND 1 18 --operator-bounds and the CaDiCaL 2.1.2 binary supplied with Lean 4.36.0. Both runs seeded two positive and two negative rows. Every decoded candidate was evaluated on all 520 tests.

| Minimum suffix AND / OR | Wall budget | Encoded rows at end | Rejected candidates | Verdict |
| --- | ---: | ---: | ---: | --- |
| 8 / 18 at parent checkpoint | 120 s | 36 | 9 | UNKNOWN |
| 9 / 18 | 180 s | 34 | 8 | UNKNOWN |

A timeout does not eliminate a branch. Even 9 AND plus 18 OR uses only 27 of the 59 free slots. The unrestricted 63-gate question remains open. No standard lease was taken, renewed or released by this session. The desk reported an existing holder. PRs 7762 and 8170 were already merged, both with accepted checker comments.

## Fifth-gate follow-up on code 888

With the fourth gate fixed to AND(1,18), 30 wires can feed the fifth gate. The 1,800 ordered fifth-gate codes select OR for k < 900 and AND otherwise, with operands (floor(k/30) mod 30, k mod 30). Run python research/order3_code888_fifth.py. For each negative pair the program finds every dominated positive among the 52 positives on the 30-wire prefix. It packs the 1,800 fifth-gate bits for each row. A gate destroys all witnesses exactly if every witness has fifth bit true and both negatives have fifth bit false. Negative pairs with no prefix witness are always rejected.

There are 56 potentially destructive operand pairs up to swapping, after excluding the always-rejected pairs. Three disjoint batches of these 56 yield negative sets of sizes 271, 258 and 261. The first 257 of each give respectively 1,728, 1,728 and 1,730 valid codes, covering 1,800 in union. The program also directly replays 32,896 pairs at each of codes 1437, 1227 and 1677 with scalar gates and no packed gate columns. This is an exact finite Python check of candidate certificates for nine ANDs after the fifth gate. There was no SAT call in this enumeration. These fifth-gate certificates have not been translated into Lean. A next run can connect the three certificates to the separating-pair theorem, handling the 31 physical wires and any two additional constants explicitly.

## Pinned Lean 4.36.0 checker

The project checker returned ACCEPTED, exit 0, for PlaneFourthOrEquivalences (1,893 rechecked constants), PlaneSecondMaskAndCount (1,983), PlaneFourthCoverage (1,919), and both PlaneFlagFamilyA and PlaneFlagFamilyB (1,987 each). Each reported only propext, Quot.sound and Classical.choice. The second mask initially encountered a verifier fault (exit 137) and subsequently passed with identical source. The coverage enumeration was split into batches after an initial build fault. The exhaustive coverage theorem and these accepted component theorems cover 1,682 fourth codes; the SAT driver requests 9 AND and 18 OR across all of them. Eleven representative encoder calls checked the signs, thresholds, and 59 remaining gate selectors.
