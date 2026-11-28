# L-meta-2625 case 35: the sixth ordinary gate after a masked point-pair OR

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

## Sixth-position exclusion for every masked third point pair

Across the 23 exceptional raw columns, separate enumerations of the dependent and independent cases found the same union of 28,611 outstanding product columns before the new certificates were added. Signed dominance reduces their union to 8,681 maximal representatives. Discovery grouped similar representatives in envelopes of at most 24, then split unfinished groups into sixes, pairs and singletons. A proposed pool only counts after replay of its integer witnesses. We kept 3,004 pools covering the full maximal set. Their replayed OR floors were 20 for 753 pools, 21 for 1,370 pools, 22 for 881 pools. Each floor exceeds the 19 available ORs.

The census rechecks all 3,342,405 common unordered independent pairs once, then tests every newly available independent pair for each choice of Y, as well as dependent ORs that read the preceding OR or its mask. A fresh census found zero residual products on each of the 23 exceptional raw columns. Together with the 209 earlier-wire substitutions above, this excludes a sixth ordinary AND for all 234 nonempty input-mask layouts. All claims in this section apply to the fixed first two ordinary operations, suffix split and test set at the top of this report.

## Unmasked pairs, arbitrary third columns and the next case

The CSV contains all 78 unordered pairs of distinct raw point wires, their exact independent/dependent counts and SHA-256 of the canonical residual. It labels 35 pairs covered by the numerical census, 1 otherwise resolved by a pre-existing physical wire, and 42 open. Refiltering the saved before-certificate frontiers for 68 raw pairs independently reproduced every byte of their newly enumerated residuals. The other ten raw pairs touch point 5 and had been handled by the parent work. Across the 42 open branches the union contains 45,497 distinct products. Of the 1,103 products in the smallest branch, 291 also occur in another open branch.

After A and X there are 2,585 distinct truth columns for a third OR of any available wires, allowing either operand to carry the guard. An existing physical wire other than wire 32 signed-dominates 1,210 of them. Allowing replacement by a resolved raw point-pair OR raises coverage to 1,244. Such a replacement uses the same third ordinary OR slot and can leave old mask wires unused. The other 1,341 are outside this dominance exclusion.

Resume from **Y = OR(4,12)**. Its residual contains 899 distinct independent products and 263 distinct dependent products, with 1,103 in their union and 522 signed-maximal representatives. The canonical decompressed bytes have SHA-256 `c6e70836cb4953711ae71307e8932250b738c5630373a8bc2b225d74128a4866` and are archived as `case35-h19-4-12-sixth-frontier-48.json.gz`. An open product is a remaining search case. The public project snapshot at 2026-11-28T10:51:41.042Z still marks the full unit as a conjecture.

Replay the ledgers, output the table, or reproduce the selected frontier from the same verified parent cache. Compare the uncompressed frontier and CSV to the archives in this directory.

```sh
python research/order3_case35_h19_masked_point_pairs.py --parent-cache /tmp/case35-parent-48.json --scope all-points --census-csv /tmp/case35-pairs.csv
python research/order3_case35_h19_masked_point_pairs.py --parent-cache /tmp/case35-parent-48.json --pair 4 12 --write-frontier /tmp/case35-frontier.json
```

Two additional direct CEGAR SAT queries used the repository-pinned CaDiCaL. They allow at least nineteen guard reads and do not fix the suffix AND/OR split. The explicitly masked third input, followed by two ORs and a sixth ordinary AND, returned **UNKNOWN, 56 encoded rows, 0 decoded candidates** at 90 seconds. The unfixed continuation after the selected raw third OR returned **UNKNOWN, 56 encoded rows, 0 decoded candidates** at 60 seconds. Solver timeouts count as UNKNOWN. To reproduce all three direct budgets from this report, run in Bash with `cadical` from the pinned Lean toolchain on PATH.

```bash
common=(
  --case 35 --third AND 15 27 --fourth AND 17 26
  --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6
  --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32
  --all-positives --negative-seed 1 --negative-seed 2
  --operator-bounds --shared-guard-budget --min-guard-reads 19
  --eleventh AND 0 17 --wire-credit --twelfth AND 0 23
  --adaptive-charge --thirteenth AND 0 25 --trace-budget
  --preloaded-trace --guard-read-ceiling --or-trace-density
  --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40
  --after-fifteen AND 7 41 --star-probes --after-fifteen AND 3 15
  --after-fifteen OR 12 42
)
python research/order3_prefix_search.py "${common[@]}" --after-fifteen OR 0 2 --after-fifteen OR 4 45 --after-fifteen OR 7 46 --after-fifteen AND 14 47 --seconds 75 --solver "$(command -v cadical)"
python research/order3_prefix_search.py "${common[@]}" --after-fifteen AND 6 32 --after-fifteen OR 12 45 --after-fifteen OR 0 46 --after-fifteen OR 9 47 --after-fifteen AND 3 48 --seconds 90 --solver "$(command -v cadical)"
python research/order3_prefix_search.py "${common[@]}" --after-fifteen OR 4 12 --seconds 60 --solver "$(command -v cadical)"
```

## Refinement of the OR(4,12) continuation

The 78-row CSV above is the fixed starting census for this refinement. Fix the fourth ordinary gate to OR(Y,t), where Y = OR(4,12) and t is any of the eleven other raw points. For each fourth gate, enumerate every fifth OR of older wires or their guard masks, then test the sixth AND on all operand pairs. An operand mask changes a raw intersection P to P AND guard, so the checker explicitly tests both columns. This includes sixth gates that ignore the most recent OR.

Before the refinement, the eleven branches had 358 distinct remaining products and 255 signed-maximal representatives across their union. New independently replayed pools total 255. Their integer OR floors are 20 for 50 pools, 21 for 113 pools, 22 for 92 pools. After replay, 11 of eleven fourth-gate branches have zero residuals. The fifth-gate counts below are distinct truth columns. The fifth OR can read any earlier wire or its guard mask.

| Fourth point t | Fifth OR columns | Fifth columns with residuals before | Products before | Fifth columns with residuals after | Products after |
|---:|---:|---:|---:|---:|---:|
| 0 | 2,848 | 61 | 56 | 0 | 0 |
| 1 | 2,847 | 54 | 51 | 0 | 0 |
| 2 | 2,856 | 11 | 6 | 0 | 0 |
| 3 | 2,850 | 55 | 52 | 0 | 0 |
| 5 | 2,857 | 6 | 6 | 0 | 0 |
| 6 | 2,854 | 11 | 6 | 0 | 0 |
| 7 | 2,854 | 7 | 7 | 0 | 0 |
| 8 | 2,857 | 49 | 47 | 0 | 0 |
| 9 | 2,846 | 53 | 49 | 0 | 0 |
| 10 | 2,857 | 49 | 47 | 0 | 0 |
| 11 | 2,857 | 52 | 50 | 0 | 0 |

The new two-preload certificates are valid without fixing that fourth OR. Applied to the unrestricted fourth and fifth ORs with third OR(4,12), the archived baseline union falls from 1,103 products to **638** (513 independent, 184 dependent, 309 signed-maximal). Fresh enumeration of the full raw pair agrees byte for byte with filtering the old frontier. This remains the smallest of the 42 open raw pairs after refiltering all their baseline sets. Resume with the updated file `case35-h19-4-12-after-attachments-48.json.gz`; its decompressed SHA-256 is `987cfe1a9ecee8463edddabb8ce61caa77bd686b4abc1022d2449dff836726de`.

The same eight-second HiGHS clique budget and exact integer replay apply to these extra pools. The 60-second direct SAT verdict for OR(4,12) remains UNKNOWN. To regenerate the updated data, run from the research checkout.

```sh
python research/order3_case35_h19_fourth_point_attachment.py --parent-cache /tmp/case35-parent-48.json --write-frontier /tmp/frontier-after-attachments.json
```

The final public status refresh at 2026-11-28T11:00:55.407Z still listed L-meta-2625 as a conjecture. Upstream main at 890bd876a5307fc2b1d3278e090bcd6842d93f9d retained the same three reductions, the same checked definitions, and the same checker. No lease was issued in this session.
