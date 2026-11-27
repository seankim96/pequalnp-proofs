# L-meta-2625 · Case 35 · interchangeable implementations after gate eight

Parent checkpoint `ea902b4fc6a24a6c788465471e159a14b4e67a75`. Checked against upstream `aecf602ea3c8da01533a13d2ca03b633689f3033` with pinned Lean 4.36.0. The desk reported `not_open` for this unit and issued no lease. Upstream has three reductions for this unit (50, 317, 487). The four account PRs were closed. PRs #7762 and #8170 were merged with accepted checks and no outstanding review changes. The 63-gate problem remains unresolved in the research record.

## Bound for every continuation of eight gates

The eight fixed gates are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24). Inputs are wires 0–25 and the seventh gate produces wire 32. Consider any suffix, arbitrary fan-out and any output wire that separates the 52 positive and 468 negative rows. Compare signals on these 520 rows.

Let F count suffix gates whose output can be realized with one AND of earlier wires and also with either one OR of earlier wires or one AND of earlier wires involving wire 32. Count each gate once. The previous theorem counted only the ANDs literally reading wire 32 (h). Every such AND contributes to F.

**PlaneCase35SemanticReuse** proves that the total number of gates is at least **35 + F**. To force eighteen ORs, replay the circuit with available single-AND implementations. To force nine non-guard ANDs, replay with available OR or guard-AND implementations. Both replays preserve all wire values on every tested row. The eighteen and nine charges belong to disjoint sets of gates outside the F counted gates. Thus size 63 allows at most 28 counted gates. If h = 28, even one more counted gate rules out the circuit.

## A formally checked boundary family

Fix gate 9 to AND(15,32) and gate 10 to AND(25,32). Of 1,332 physical choices for gate 11 (two operators and unordered legal input pairs with repetition), 237 use no explicit guard AND and have both implementations. The physical choices comprise 60 ORs and 177 ANDs. Four create a nonzero signal absent from the earlier wires. For example, AND(6,28) agrees with AND(28,32) on all 520 rows.

**PlaneCase35BoundaryCodes** takes the size theorem as its explicit premise. Applying it to **PlaneCase35SemanticReuse** proves, for each index of a 237-entry explicit array and any following gates, that 38 plus the number of guard ANDs *after* gate 11 is at most the total circuit size. At h = 28 there must be 26 such ANDs after gate 11. Therefore all 237 choices require at least 64 gates. The Lean certificate compares packed row values with both concrete replacement gates. An independent Python enumeration checked distinctness, compared the complete ordered code list to the Lean array and reproduced the count. The 1,095 other choices remain open under this test.

The Python census extends the rule to two gates. Of 1,872,792 ordered choices of gates 11–12, 612,696 contain a disallowed extra counted gate at h = 28, including extensions of the 237 first-step exclusions. This second census is computational. The explicit Lean table ends at gate 11. Replay with `python research/order3_case35_semantic_reuse.py`.

## Bounded exact-synthesis attempts

Each CaDiCaL run sought a size-63 solution and started with positives 0–51 and negatives 0, 1, 2 and 234. A decoded candidate would be tested on all 520 rows. Each run finished with 56 encoded rows and zero decoded candidates. The fixed-eight run imposed no minimum guard count. All runs used the existing operator and shared-guard lower bounds.

| Fixed gates | Additional constraints | Variables | Clauses | CEGIS wall budget | Verdict |
| --- | --- | ---: | ---: | ---: | --- |
| 1–8 | At most 28 counted gates | 19,580 | 587,955 | 150 s | UNKNOWN |
| 1–10 | At least 28 guard reads and no extra counted gate | 18,868 | 569,598 | 120 s | UNKNOWN |
| 1–11, gate 11 = AND(0,1) | Same boundary constraints | 18,460 | 561,114 | 90 s | UNKNOWN |

To reproduce, use the Lean toolchain's `bin/cadical` and the following common command. Append the corresponding flags from the table below. The budget encoder recognizes a subset of all interchangeable implementations using fixed earlier wires, explicit guard ANDs, and repeated operands. This is sound for physical circuits represented by one-hot operand selectors. Independently evaluating the new exclusion clauses in both operand orders matched the full-row classification on every next-gate choice after 8, 10 and 11 fixed gates (2,312, 2,592 and 2,738 ordered choices).

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --solver PATH_TO_PINNED_CADICAL
```

| Fixed gates | Append |
| --- | --- |
| 1–8 | `--semantic-budget --seconds 150` |
| 1–10 | `--ninth AND 15 32 --tenth AND 25 32 --min-guard-reads 28 --semantic-boundary --seconds 120` |
| 1–11 | Same as 1–10, adding `--eleventh AND 0 1` and using `--seconds 90` |

Next unresolved example: gates 1–10 as above, gate 11 = AND(0,1), h = 28. At that prefix 52 gates remain. The Python sweep marks 262 of its 1,406 possible twelfth gates, including 24 that directly read the new wire 36. A follow-up can formally certify which twelfth-gate choices are excluded, or investigate when the remaining costly gates can attain the two lower bounds simultaneously. None of the three solver runs produced a proof or a separating circuit for the unrestricted problem.


## Replaying the composition

The two proof files can be checked separately. The following Lean expression applies the classifier to the gate bound and leaves no size-bound premise. The recorded external statement for each file lives under `research/statements/`.

```lean
import PEqualNP.Research.PlaneCase35SemanticReuse
import PEqualNP.Research.PlaneCase35BoundaryCodes

#check PEqualNP.Research.PlaneCase35BoundaryCodes PEqualNP.Research.PlaneCase35SemanticReuse
```

| Standalone theorem | Project checker | Rechecked constants | Single-file diff from checked upstream |
| --- | --- | ---: | --- |
| PlaneCase35SemanticReuse | ACCEPTED (check) | 2,243 | [comparison](https://github.com/seankim96/pequalnp-proofs/compare/aecf602ea3c8da01533a13d2ca03b633689f3033...6dc4529a7261e45929447b565bade24c1a151dd9) |
| PlaneCase35BoundaryCodes | ACCEPTED (check) | 2,068 | [comparison](https://github.com/seankim96/pequalnp-proofs/compare/aecf602ea3c8da01533a13d2ca03b633689f3033...f9654467ee678cdda995289d7b6843cfb341f8bc) |

Both manifests listed only their own research module and 87 definition modules matching upstream byte-for-byte. The two independently expanded statements also compiled, as did the combined theorem against its unconditional statement. Its transitive axioms were propext, Quot.sound and Classical.choice. Earlier monolithic kernel checks ended with exit 137. Splitting the proofs and checking the finite witnesses in batches produced both final ACCEPTED verdicts. No upstream PR was opened for this unleased unit.
