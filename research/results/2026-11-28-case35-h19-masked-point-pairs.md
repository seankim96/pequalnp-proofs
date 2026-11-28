# L-meta-2625 — Closing the remaining sixth AND after OR(0,2)

Parent research commit cedac677b67476d2aadcb96861017baab300b83c. The project's 2026-11-28 10:20:39 UTC snapshot still lists L-meta-2625 as a conjecture. Upstream 8b3771bb237ff5671e3d9dc90f7cfc002ad34183 contains the three existing reductions 50, 317 and 487. The targeted desk returned no lease. The account has no open upstream PR, and both #7762 and #8170 have merged with accepted checks and no requested changes.

Use case 35's original 17 physical gates, total size 63, exactly nineteen physical reads of guard wire 32, ten ordinary ANDs and nineteen ORs in the suffix. Positions below skip physical guard ANDs. Fix A = AND(3,15), X = OR(12,42) and Y = OR(0,2), followed by any two ORs. The sixth non-guard gate must also be an OR. This is a restricted, certificate-backed numerical exclusion on all 52 positive and 468 negative inputs.

The previous frontier had 1,899 distinct candidate products. Its SHA-256 was verified before selecting 561 signed-maximal representatives. For each representative P, two preloaded columns can supply A and P, directly or after a guard mask. The relaxation retains eight ordinary ANDs and nineteen ORs. The independently replayed integer OR floors were 20 for two pools, 21 for 51 pools, and 22 for 508 pools. The union of the independent and dependent residuals fell from 1,899 to zero. Another 111 replayed certificates target input-masked variants of the third OR. The two compressed ledgers contain all 672 records.

For the direct SAT cross-check use the three-query Bash recipe in the parent report, retaining `common` and fixing the following gates. This query permits at least nineteen guard reads, without the fixed ordinary split. Pinned CaDiCaL at 75 seconds returned UNKNOWN with 56 encoded rows and no decoded candidate.

```sh
python research/order3_prefix_search.py "${common[@]}" --after-fifteen OR 0 2 --after-fifteen OR 4 45 --after-fifteen OR 7 46 --after-fifteen AND 14 47 --seconds 75
```

Negative-clique discovery used an eight-second limit per HiGHS optimization. The per-negative packing on the 52 positive flags had no separate solver deadline. Only independently replayed integer witnesses count. To replay the certificates and the exact parent frontier, run the following command in the research checkout. An absent cache is regenerated from the inherited witness ledgers.

```sh
python research/order3_case35_h19_masked_point_pairs.py --parent-cache /tmp/case35-parent-48.json
```

## Reducing 234 masked third ORs to 23 distinct truth columns

Let i < j be two of the thirteen point wires. The third non-guard OR may read i through guard wire 32, j through the guard, or both. Count the 78 unordered pairs separately for each of the three nonempty mask patterns. Subsequent fourth and fifth ORs and the candidate sixth AND can also use guarded operands.

For 209 of the 234 layouts, a physical wire already present before the third OR signed-dominates its output: it is true on every positive on which the third OR is true and is false on every negative on which the third OR is false. The donor is always a physical wire other than wire 32. Redirect the consumers of Y to that donor. Positive outputs can only increase and negative outputs can only decrease. The now-unused Y can move just after the candidate AND, with the other gates relabelled in topological order. This changes neither the physical gate counts nor which ANDs read the designated guard wire. It would put the ordinary AND at position five after A,X, which the previous checkpoint excluded for arbitrary intervening ORs.

| Inputs masked | Layouts | Direct dominating wire other than 32 | Remaining |
|---|---:|---:|---:|
| Left | 78 | 62 | 16 |
| Right | 78 | 70 | 8 |
| Both | 78 | 77 | 1 |

In each of the 25 remaining layouts, Y has exactly the same 520-bit column as the unmasked OR(i,j). They give precisely the 23 unordered point pairs touching point 2 or 6. Guard 32 is OR(2,6): these are the only two raw point columns unchanged by masking. On the 52 positives, masking any other point produces no true bit. The numerical classifier additionally checks all 468 negative bits. Equality of third columns permits the same relaxed sixth-position census regardless of whether the physical realization spent guard reads to make Y.

## Linear support for a shared-guard OR schedule

For a block of any length containing k binary ORs and any number of masks by the same Boolean guard, every output is an OR of at most k+1 tagged original wire occurrences. A tagged occurrence contributes its input directly or conjoined with the guard. The same tagged list works simultaneously on all rows and both values of the guard. Sharing, repeated destinations, arbitrary initial wire states and an arbitrary output label are allowed. In particular, the output of a two-OR block needs at most three original wire occurrences.

The proof traces a list of demanded occurrences backward. If the written destination is demanded several times, combine all those demands first: an unmasked demand takes priority. An OR replaces those occurrences by at most two operand occurrences and increases the list length by at most one. A guard mask replaces them by one guarded occurrence. An unused write costs nothing. Starting from a single output gives the asserted bound.

The repository-pinned Lean 4.36.0 checker returned ACCEPTED (check) for PlaneLinearGuardedOrSupport, with 1,723 kernel-rechecked constants and axioms propext, Quot.sound and Classical.choice. The 87 definition hashes in the checker manifest matched upstream 8b3771bb237ff5671e3d9dc90f7cfc002ad34183, and an independent import checked the exact statement and axiom list. The single-file proof commit on the fork is 248f0e00ef8f1d291f7c2e59110d467fca2dbc6b. This theorem covers OR-and-mask blocks. The full-circuit lower bound is open.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneLinearGuardedOrSupport.lean research/statements/PlaneLinearGuardedOrSupport.txt check
```
