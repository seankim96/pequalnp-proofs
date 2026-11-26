# L-meta-2625 — uniform fourth-gate bound for case 35

Parent ebc2ad9e737992ae78a600bdbd6e2af0feaf014b on research/circuit-lower-bounds. Indexing is zero-based. The first two gates are OR(0,1) and OR(3,9). Gates three and four may use either operation and any earlier wires, with repetitions and unrestricted fanout. Test all 52 positive flags and 468 negatives. The gates after the fourth may also read the Boolean constants. There are 659,344 ordered operand choices for each fixed pair of operation types.

## Lean results

**PlaneCase35AnyLines.** The pair certificate from the parent transports to all 78 unordered pairs of distinct projective lines. For any chosen pair, every added signal that is true on a positive flag outside those lines must have a true baseline wire whose truth on negative inputs implies that signal. Under this condition every successful suffix needs at least nine AND gates. The transport uses three relabelings. Their action on the 28-bit signatures first permutes the 26 raw bits, then recomputes the original two OR outputs. It preserves bitwise union. Lean checks the positive and negative row maps, the line maps and a path of at most seven generators to each requested pair.

**PlaneCase35FourthWitnessTypes** verifies the witness-type hypotheses for every third and fourth gate. **PlaneCase35UniformFourth** combines that result with the two-line certificate and the OR cut. Every one of the 2,637,376 ordered choices for gates three and four satisfies the two-line hypothesis for some pair of lines. The suffix after the fourth gate requires at least nine AND gates. The previous OR cut gives at least 18 OR gates after the second gate. Combining the two statements gives the following total gate lower bounds within case 35.

| Gates three and four | Minimum ANDs after gate four | Minimum ORs after gate four | Minimum total gates |
|---|---:|---:|---:|
| OR, OR | 9 | 16 | 29 |
| AND, OR or OR, AND | 9 | 17 | 30 |
| AND, AND | 9 | 18 | 31 |

For a positive flag the single point and the single line give two possible baseline witnesses. Outside the excluded lines we give each added gate one witness type. If its output is true, setting the corresponding raw witness on any negative forces the gate true there as well. Gates with both operands of the same witness type preserve that implication. Excluding a line makes that input false on retained flags. The choice of two lines and two witness types is reduced to 64 Boolean configurations: four operand types and two possible references to gate three. The theorem quantifies over operand indices and both operations, so the circuit bound requires no external enumeration. The expanded statements and run verdicts below distinguish individual module checks from the combined replay.

Pinned Lean 4.36.0. The project checker accepted the three independently replayable steps in check mode. Their full manifests were compared to the fork sources and all 87 upstream definition modules.

| Project check on the stated research proposition | Verdict | Constants rechecked |
|---|---|---:|
| PlaneCase35AnyLines (transport) | ACCEPTED | 2,334 |
| PlaneCase35FourthWitnessTypes (unconditional existence of the required witnesses) | ACCEPTED | 1,907 |
| PlaneCase35BudgetComposition (both preceding statements plus the previously accepted OR cut imply the final bound) | ACCEPTED | 1,721 |

The modular final theorem PlaneCase35UniformFourth directly applies the composition lemma to those two proofs and PlaneCase35OrCut (accepted at the parent, 1,843 constants). The separate file PlaneCase35Independent contains the complete proof with only Mathlib imports. Both built on the pinned toolchain. For each, `lake env leanchecker -v PEqualNP.Research.<name>` replayed the module's declarations and exited 0. Lean also type-checked both theorems against the same expanded statement. Both use exactly propext, Classical.choice and Quot.sound. The project verifier also tried a full replay for each complete version. In both cases the file built and the verifier then exited 137; the project checker reported FAULT, with no whole-file acceptance. The three accepted component checks and the toolchain kernel replays are the positive verdicts.

To reproduce the project checks from the fork root, use `node tools/check-lean.mjs lean/PEqualNP/Research/<name>.lean research/statements/<name>.txt check`. Run leanchecker from the lean directory after building the module.

## Finite replays and fifth-gate follow-up

Run python3 research/order3_case35_singletons.py. For each gate evaluate a full flag, the point alone and the line alone. A mixed exception is a flag accepted only on the combined input. The exact counts of ordered extensions with exceptions on zero, one and two lines are 2,212,612, 408,204 and 16,560. This corroborates the structural theorem.

As a separate experiment, fix AND(15,27), AND(17,26) after the two ORs. Their positive supports are precisely flags 9 and 16 (lines 2 and 4). The previous first-two-line rule missed both gates. Run python3 research/order3_case35_fifth_15_17.py. It checks every one of the 1,800 ordered choices for gate five. There are 55 distinct exception masks relative to the actual 30 wires, each containing at most two flags. For each mask the negative-pair calculation retains between 408 and 444 negatives. The earlier slice catalogue supplies 19 positive flags for every fifth gate. These are finite Python checks furnishing witnesses for a possible nine-AND and eighteen-OR bound strictly after the fifth gate. Formalizing that fifth-gate bound is a next step.

## 63-gate searches

CaDiCaL 2.1.2, 26 raw inputs, two-input gates with unrestricted reuse. Each run started with all 52 positives and negative indices 0 and 234, then validated decoded candidates against all 520 labels. The bounds option now applies the fourth-gate theorem throughout case 35. With a fifth gate specified it subtracts its operator from the remaining budget.

| Gates after the two ORs | Free slots | Suffix bounds | Initial variables / clauses | Time limit | End rows / decoded candidates | Result |
|---|---:|---|---|---:|---|---|
| AND(16,26), AND(23,27) | 59 | none | 16,579 / 580,024 | 90 s | 54 / 0 | UNKNOWN |
| AND(15,27), AND(17,26) | 59 | 9 AND, 18 OR | 18,172 / 583,094 | 120 s | 56 / 1 | UNKNOWN |
| AND(15,27), AND(17,26), AND(19,27) | 58 | 8 AND, 18 OR | 17,864 / 573,096 | 90 s | 54 / 0 | UNKNOWN |

Reproduce with research/order3_prefix_search.py, --case 35 --all-positives, the indicated --third, --fourth and optional --fifth gates, --seconds and --solver; specify --operator-bounds for the last two. There is no successful 63-gate witness or exclusion from these time-limited searches.

## Desk and GitHub

Upstream main was b3977e8d3a26165630183a95eb5a2fbd5b82a523 at the project check. The desk returned not_open for L-meta-2625 (accepted or stood down); main contained the three existing reductions R_meta_2625_317, _487 and _50. No unrestricted verdict was identified. The account's four existing upstream PRs were closed. #7762 and #8170 were merged, had no reviews or inline review comments, and each had checker exit 0 reported by the intake bot. The current work was recorded on the fork; no standard assignment lease was taken, renewed or released and no upstream PR was opened.
