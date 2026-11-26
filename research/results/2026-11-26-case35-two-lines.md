# L-meta-2625 — case 35 after the two point OR gates

Fork parent `a9d3cf9a717031ff669d1f7d0f279640af9323d8`. Upstream checked at `ee086f00f54d03286d6ff169747677d331ae65bd`. Case 35 starts with OR(0,1), OR(3,9). Allow either binary operation at gates three and four, ordered operands, repeated operands, reuse of the third result at the fourth gate, unrestricted suffix wiring, and both Boolean constants for the suffix. The labels are the same 52 positives and 468 negatives as in the predecessor.

## Kernel results

* **PlaneCase35EightFlags** selects 257 negatives. For every pair it supplies a positive flag outside the eight flags of lines 0 and 1 that is contained in the union of the pair on the 28 baseline wires. The compressed certificate uses 28 residual masks. The public `pairCertificate` exposes the witnesses. Any additional wires that inherit a baseline witness on every positive outside those eight flags preserve the nine-AND suffix bound.
* **PlaneCase35OrCut** fixes negative index 159 and 19 positive flags. Each baseline wire that rejects this negative accepts at most one selected flag. On this slice an AND can take its support from one rejecting predecessor. An OR may combine two supports. The union for a collection of wires grows by at most one extra flag per OR. An output passing all 520 tests therefore needs at least 18 ORs **after the second gate**, for every third/fourth choice.
* **PlaneCase35GuardedPair** gives a joint bound after imposing a condition on each of gates three and four. The condition holds for any OR, for equal input columns, and for an AND that is false on positive flags 8 through 51. If both gates satisfy it, the suffix after gate four has at least nine ANDs. The circuit has at least **29 plus the number of ANDs among gates three and four** gates in total.
* **PlaneCase35LineAnd** specializes the last result to two ANDs each having line input 13 or 14 as its left operand. The right operands range over all 28 and 29 previous wires. This directly proves at least **9 ANDs and 18 ORs after gate four**, hence **31 total gates**, for 3,248 ordered choices. This includes the previous worst example AND(13,26), AND(13,27) and the solver branch below.

Verification used the repository toolchain `leanprover/lean4:v4.36.0` and `node tools/check-lean.mjs lean/PEqualNP/Research/<name>.lean ../pgr21/research/statements/<name>.txt check` in the upstream checkout with the research dependencies overlaid. In a fork checkout use `research/statements/<name>.txt` for the second argument. The exact expanded statements are in this commit. Hashes of every research module in each accepted manifest were matched to the fork files. All 87 definitions per manifest were matched to upstream. Only propext, Quot.sound and Classical.choice occur.

| Theorem | Verdict | Kernel-rechecked constants |
|---|---|---:|
| PlaneCase35EightFlags | ACCEPTED (check) | 2,054 |
| PlaneCase35OrCut | ACCEPTED (check) | 1,843 |
| PlaneCase35GuardedPair | ACCEPTED (check) | 2,099 |
| PlaneCase35LineAnd | ACCEPTED (check) | 2,105 |

## Finite replays

Run the three scripts with Python 3 and assertions enabled. These counts are Python results. The Lean theorem proves the implication for every circuit satisfying its stated hypotheses.

* `research/order3_case35_third.py` counts **2,253,044** of the 2,637,376 ordered extensions passing the sufficient syntactic test (OR, identical operand indices, or zero AND outside the first eight flags). Counts by types (third, fourth) are AND/AND 481,230, AND/OR 560,106, OR/AND 552,364, OR/OR 659,344. The larger semantic inheritance test on these two lines covers 2,280,900 extensions and 50 exception masks. Across the full enumeration the number of distinct masks supported on zero, one or two lines respectively is 1, 135 and 1,344.
* `research/order3_case35_line_pairs.py` transports the 257-row certificate to every one of the 78 unordered pairs of projective lines. It checks label preservation for every permutation and reevaluates all 32,896 pair witnesses on the original 28 baseline wires for each line pair (2,565,888 checks). This supplies a numerical route for extending the nine-AND argument to all 1,480 exception masks.
* `research/order3_case35_or_slices.py` verifies a catalogue of 36 negative/19-flag slices directly on the 30 actual wires. In 2,633,616 extensions at least one slice keeps all 19 flags. Each of the remaining 3,760 admits an 18-flag slice by removing one flag. These witnesses suggest a suffix lower bound of 18 ORs for the former and 17 ORs for the latter strictly after gate four. The catalogue and its coverage have yet to be formalized.

## SAT replay

For a total of 63 gates fix third AND(13,27), fourth AND(14,26). The remaining 59 binary gates can reuse earlier wires. CaDiCaL 2.1.2 started with all positives and negative indices 0 and 234; each decoded candidate was evaluated on every one of the 520 labels. Both runs reached their limits after one invalid decoded candidate and two counterexamples added (56 active rows).

| Suffix thresholds | Initial variables | Initial clauses | Time budget | Verdict |
|---|---:|---:|---:|---|
| None | 16,579 | 580,024 | 90 s | UNKNOWN |
| ≥9 AND, ≥18 OR | 18,172 | 583,094 | 120 s | UNKNOWN |

Use `research/order3_prefix_search.py --case 35 --third AND 13 27 --fourth AND 14 26 --all-positives --seconds 90 --solver <cadical>`. Add `--operator-bounds` and change the budget to 120 for the second run. The solver now applies the case-35 bounds when that flag is selected and the corresponding checked hypotheses hold.

## Project state and handoff

The desk returned `not_open` for L-meta-2625. Upstream contains the previously posted partial reductions, and we found no proof or counterexample settling the unrestricted 63-gate question. The existing PRs from seankim96, including #7762 and #8170, were merged with no actionable review changes in those two. This run was fork-only research. It acquired no lease, changed no other session’s lease and opened no upstream PR.

For the next session, use the public pair certificate and the 78 label permutations to formalize transport to arbitrary line pairs. The remaining step to a uniform nine-AND suffix theorem is to connect the two-line exception condition to both gates for every extension. A separate route to a better OR bound is to formalize the smaller 18-flag witnesses for the 3,760 residual extensions. The unrestricted 63-gate result remains open in these computations.
