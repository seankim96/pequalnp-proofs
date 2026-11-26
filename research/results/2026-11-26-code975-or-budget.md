# L-meta-2625: sixth AND family 5 and OR discrimination

Parent 12d644bed665b9f357d6292caa5fb5fe208e3d80. On November 26, 2026 the desk listed the parent open. Upstream main still had the three reductions 50, 317 and 487 and no final parent proof. PRs 7762 and 8170 were already merged. This is independent research on the fork. No official lease acquired, renewed or released.

Fix AND(0,13), OR(0,14), AND(1,13), AND(1,18), AND(2,15), followed by an AND with ordered inputs (l,r). Its code is 31*l+r. The domain has 52 positive rows and 468 negative rows. Suffix gates may reuse any prior wires.

* Plane975Family5Codes: ACCEPTED by the project checker (check mode, Lean 4.36.0, 2,012 kernel constants). With omitted positive mask 0x88f8000008000 the twelve new codes are 209, 333, 364, 384, 396, 397, 719, 723, 724, 736, 756, 787. At least nine AND gates must follow each. The checked coverage for this AND bound advances from 925 to 937 of 961. Next family 6 contains eight of the remaining 24 choices.
* A separate CaDiCaL 2.1.2 run fixed code 209 = AND(6,23) with 57 unrestricted monotone suffix slots, seeded all 52 positives and the two negative rows at combined indices 52 and 286. 16,131 variables and 560,364 clauses. Budget 45 seconds. Zero models returned; UNKNOWN (timeout). No SAT-based branch exclusion.
* A finite replay also tried every unordered first OR on raw input wires (repetition allowed). For each positive pair x,y it asked for a negative z containing their common input bits and satisfying the OR if both x,y satisfy it. After dropping at most one positive row, every remaining pair had a witness. Of 351 choices, 195 retain all 52 and the other 156 retain 51. For OR(0,14) all 52 survive. The script tests 465,426 combinations; this general first-OR census is numerical.

## Six OR gates after every sixth AND

PlanePositiveOrBudget: ACCEPTED (check), 1,720 constants. For 33 positive rows it suffices that every pair has a negative row which is true on all columns common to that pair. Recording the first input bit of each OR during evaluation yields distinct binary traces for those 33 positives. With at most five OR gates there are at most 32 traces. AND gates are unrestricted.

Plane975SixthAndOrBudget: ACCEPTED (check), 1,741 constants. A packed witness table for all 528 pairs among the first 33 positive rows verifies the condition on the fixed 31 columns and two constants. Appending the AND of any two wires preserves it. Therefore at least six OR gates are required in any correct suffix, simultaneously for all 961 ordered choices of the sixth AND. In the 937 cases already carrying the separate nine-AND lower bound, at least 15 more gates are necessary (21 total including the prefix). This is a restricted lower bound, and 63 gates remain unresolved.

All three runs used the pinned project checker in check mode with the permitted axioms propext, Quot.sound and Classical.choice. Research-module/definition manifest counts were 4/86, 3/86 and 4/86 respectively, checked against disk. The official checker, verifier and Lean pin matched upstream f5a6ffe95abe74514dd225e5a6cc4770bc525197. No SAT solver used for the three kernel proofs. Next AND family mask 0x20001000f2040: 87, 128, 141, 172, 531, 532, 544, 777.
