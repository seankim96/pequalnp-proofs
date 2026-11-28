# L-meta-2625 — Least signed preloads with optional guard reads

Start at 81bd89040b830230b115d4beb122509ef4d86a1a. Fix case 35, its previously specified 17 physical gates, 63 gates in total, exactly nineteen physical guard reads, and the suffix split of ten ordinary ANDs and nineteen ORs. The finite test set is the original 52 positive and 468 negative inputs. The question here is whether the first three non-guard operations can have order AND–OR–AND, with arbitrary intervening guard masks. The parent census reduced this question to 16,131 triples of truth columns (A,X,P), spanning 9,482 pairs (A,X). They represent the first product, middle OR and third product.

## A least common supplier

Write G for the guard. A column supplies a requested wire when it has at least the requested positive bits and at most the requested negative bits, possibly after taking its AND with G. A separate choice of masked or direct read is permitted for each requested wire. The mask choice for that wire must be fixed across all test rows.

Given a family of requested columns, mark each member safe if every one of its positive bits lies on a guard-true row. Construct one signed envelope. On each positive row, its bit is the union of the required bits. On a negative row, its bit is the intersection of the requirements whose reads are active there. A safe wire can be masked, so it is inactive on a guard-false row. Every unsafe wire has to be read directly. An empty intersection gives true.

The envelope supplies the family by masking exactly the safe members. Conversely, any feasible mask assignment can mask only safe members. Every common supplier must dominate the envelope on both signs, even if its chosen mask assignment differs. Consequently, for any separator-existence predicate increasing in the signed supply order, an impossible stronger pool supplying the family exists exactly when the envelope itself is impossible. This proves optimality for the stated single-preload relaxation; it makes no realizability assumption about synthetic columns.

Lean 4.36.0 checked this theorem as `PEqualNP.Research.PlaneLeastGuardPreload`. Official verdict **ACCEPTED (check)**, with no axioms and 1,715 kernel-rechecked constants. A separate exact-statement import and axiom check passed. The 87 project definition hashes matched upstream 34b409d7899bbd1da475325f80aa1614232139d8. Single-file fork commit 1a9545f1427a95490e418188b0b4e6cd872b345f.

## Case search

First fix A = AND(3,15). Its 173 outstanding triples contain 117 middle OR values and 151 distinct third products. Signed dominance leaves 109 maximal products. For each representative, grant A and the product as two starting wires. The eight-ordinary-AND relaxation can reconstruct the middle OR within nineteen ORs. Independent replay gives floor 20 for four representatives, 21 for 36, and 22 for 69. One of the four floor-20 records uses a 128-negative clique, a 105-negative guard-false clique and the parent's strengthened operand-trace checker. All 173 target triples are thereby excluded.

For the larger search, cluster first products at each fixed third product. Choose the next member by positive overlap and retained common negative requirements. Grant the least envelope for the cluster as the first free column. Grant the third product or its singleton envelope as the second. Refine unresolved clusters at widths four, two and one. Synthetic starting columns and all their guard masks are free in the relaxation. If the two supplied columns cover A and P, a floor of twenty excludes the order. If they cover X as well, removing that OR leaves eighteen ORs, and a floor of nineteen suffices. Both uses are checked separately from the grouping heuristic.

Discovery used HiGHS with an eight-second limit per negative-clique optimization, and no separate time limit on each finite 52-flag packing. Only independently replayed witness bounds count as exclusions. A separate pinned CaDiCaL test fixed AND(3,15), OR(12,42), AND(24,44) after the same 17-gate prefix, using at least 19 physical guard reads with no fixed ordinary gate split. At 90 seconds the result was **UNKNOWN** with 56 encoded rows and zero decoded candidates.

## Closure of the AND–OR–AND order

All 16,131 remaining triples are excluded. There are zero remaining middle-OR pairs out of the checkpoint's 9,482. Across the inherited 65 normalized first products and 165,204 prefix pairs, no AND–OR–AND continuation survives this gate split. In the same split, checkpoint c97920bc already excluded two initial ordinary ANDs. It follows that if the first non-guard gate is AND, the next two non-guard gates must both be ORs.

There is also a dependency consequence for the next search. Let B be the second ordinary AND in a suffix beginning with an ordinary AND A. Then at least two distinct suffix ORs must be ancestors of B. Otherwise take the predecessor closure of A and B, keeping the guard-mask gates in that closure. Its only ordinary ANDs are A and B. A has no suffix OR ancestors, and B has at most one. Schedule A and its prerequisites first, then the other prerequisites of B, then B. The new order starts AND–AND or AND–OR–AND. Moving the unused gates later is a topological reordering: it preserves each operand edge, the output, and the physical guard count. Both resulting orders are excluded. A suffix starting OR–AND–AND has a related restriction: each of those two ANDs must depend transitively on the initial OR, since any independent one could be moved before it.

| Discovery stage | Outstanding triples after stage |
| --- | ---: |
| Previous checkpoint | 16,131 |
| Initial standard pool tests | 12,706 |
| Width-four pools | 9,764 |
| Width-two pools | 1,754 |
| Singleton pools | 390 |
| Include strengthened witnesses | 0 |

The four standard phases evaluated 958, 1,973, 2,375 and 808 candidate pools respectively. The targeted strengthened witness and 197 further operand-trace checks covered the final stage, including overlaps. The 197 further checks each reached a floor of 20. A compact replay ledger retains 2,502 distinct pairs, including all maximal-product representatives for the AND(3,15) check and 180 strengthened records. Replaying the 2,502 records gave floors of 20 for 907 pools, 21 for 1,373 and 22 for 222. Every excluded triple was covered while retaining the full nineteen-OR budget. The empty residual JSON has SHA-256 `4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945`. An exploratory three-column run on the 390 last-stage triples is dispensable: it returned standard floor 18 twice, 19 fifteen times, 20 on 104 attempts and 21 on 54 attempts. Its 215 remaining attempts produced no standard floor. No exclusion in the published census uses those three-column results.

Outside the additional fixed-prefix result below, an unfinished direction is an AND–OR–OR prefix followed by a second ordinary AND whose ancestor set contains both ORs. The OR-first orders also remain candidates subject to the dependency rule above. These finite exclusions leave case 35 and the unrestricted at-most-63-gate existence question open.

## Two specified starting operations force three consecutive ORs

In the same split, fix the first two non-guard operations as A = AND(3,15) and X = OR(12,42), using the unmasked operands at those indices. The third is an OR by the full order result. **The fourth must also be an OR.** Thus the non-guard sequence begins AND–OR–OR–OR even when physical guard ANDs intervene.

Let Y be the third operation. If Y does not read X or its mask, it uses two of the prefix columns, A, or their guard masks. There are 2,517 distinct Y values and 1,506 distinct intersections with X. A fourth ordinary AND would have to depend on both ORs by the dependency result. Its only possible output is X AND Y, optionally masked. The 2,502 two-source certificates left 415 such Y values and 281 different intersections. Seventeen maximal intersections under signed dominance suffice to cover them all.

If Y reads X directly or through its mask, there are 144 Y values. These may overlap the first group; together the two groups contain 2,585 distinct truth columns. Every possible fourth ordinary AND must now read Y directly or through its mask. Its other operand gives a product Y AND v up to masking, where v is a prefix column, A, X, or Y. A certificate supplying A and the product eliminates both ordinary ANDs. Alternatively, a product already supplied by an earlier wire or by its mask can be deleted while preloading A; the original X and Y can still be built within the nineteen-OR budget. Before the seventeen extra pools there were 172 unchecked (Y, product) pairs. After those pools there were 104 pairs and 92 distinct products. Fifty-three maximal products cover the remainder. Independent replay of all seventy additional records gave OR floors of 20 twice, 21 on 35 records and 22 on 33 records.

For this fixed prefix, an unfinished direction is the fifth non-guard gate, following the three forced ORs. For the broader branch one can instead vary the first product or first OR and compare the possible fourth ANDs. The fourth-gate exclusion here uses the exact named first two operations.

## Reproduction

Run `python research/order3_case35_h19_guard_envelopes.py` at the fork root. It replays the parent census, verifies the new finite trace records, and compares the full set of residual triples from two implementations. One uses the signed singleton envelopes. The other uses explicit comparisons against each of the two columns and both guard masks. An optional `--parent-cache` accepts the canonical sorted parent JSON only when its SHA-256 matches. Use `--write-frontier FILE` to export the sorted residual triples and compare their digest with the checkpoint. Use the parent's own `--recheck-parent` switch to replay its inherited two-source witness ledger as well.

The pin is recorded in `lean/lean-toolchain`. From a checkout using the pinned toolchain, the broader solver query can be repeated with

```sh
solver="$(cd lean && lean --print-prefix)/bin/cadical"
python research/order3_prefix_search.py --case 35 \
  --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 \
  --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 \
  --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 \
  --operator-bounds --shared-guard-budget --min-guard-reads 19 --eleventh AND 0 17 --wire-credit \
  --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget --preloaded-trace \
  --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 \
  --after-fifteen OR 39 40 --after-fifteen AND 7 41 --star-probes \
  --after-fifteen AND 3 15 --after-fifteen OR 12 42 --after-fifteen AND 24 44 \
  --seconds 90 --solver "$solver"
```

## Desk and upstream

The public unit status was `conjecture` at the 07:28:45 and 07:57:56 UTC snapshots on 2026-11-28. Upstream at 34b409d7899bbd1da475325f80aa1614232139d8 and again at e3b20a3a4b28fd67f9c7dc108eb686b3ff600a52 contained the three cuts R_meta_2625_50, R_meta_2625_317 and R_meta_2625_487. Both requested PRs, 7762 and 8170, were merged with accepted checks. The desk returned no lease for this unit. There was no lease to renew or release and no upstream PR was opened.
