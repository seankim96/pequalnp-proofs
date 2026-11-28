# L-meta-2625 — Fifth non-guard operation after AND(3,15), OR(12,42)

Use the 17 physical prefix gates of case 35, 63 total gates, exactly nineteen physical guard reads, and ten ordinary ANDs plus nineteen ORs in the suffix. Use all 52 positive and 468 negative tests. Start the suffix with A = AND(3,15) followed by X = OR(12,42), with no operand masking on those two specified operations. Arbitrary guard operations can intervene thereafter. The previous checkpoint f033e594 excludes a third or fourth ordinary AND after those starting operations. Write Y and Z for the next two ORs.

**The fifth non-guard operation must be an OR.** Within this budget split every continuation of A, X therefore starts AND–OR–OR–OR–OR. The two intermediate ORs may be any allowed values and may use guard masks. This strengthens the fixed-OR(5,10) result at ad5be93a1ed11bec9b895da23f6d1287d4e24c19.

## Fifth-gate enumeration

If the fifth operation P were an ordinary AND, both Y and Z would have to be ancestors of P. An unused Z can be moved later, producing an excluded fourth ordinary AND following A, X and Y. If Z does not depend on Y and P does not use Y, move Y later instead. This preserves all physical gates and guard reads. When Z reads Y, P may depend on Y through Z alone.

*Independent ORs.* Both Y and Z can take previous sources from the 17-gate pool, A, X, or their guard masks. There are 2,585 OR truth columns and 3,342,405 unordered choices with repetition. Interchanging Y and Z does not affect their intersection. The fifth AND must produce Y AND Z up to a final guard mask. Deleting products already supplied by an operand or its mask leaves 959,321 distinct truth columns. The eligible preloads in the parent plus the fixed-OR(5,10) milestone reduce this to 66,828 columns. Of these, 4,524 are maximal under signed dominance. Discovery tested each maximum with its own pool.

*Dependent ORs.* Let Z read Y or its guard-masked value on at least one operand. The other input is an older column, Y, or a guard-masked read thereof. Enumerate the 319,145 ordered (Y,Z) choices in this branch independently, including coincidences with the independent branch. The fifth AND must read Z, with its other operand older than Y, Y itself, or Z. The last option can be deleted. Project a product with a guarded operand onto the corresponding raw product followed by a guard mask. This permits testing the normalized products directly. A signed-dominating old source, Y, Z or their masks can replace an AND. The search selected 806 additional maximal products using the projected coverage of the independent candidates. The final verifier recomputes the frontier using only checked OR floors.

*Witness.* Preload suppliers for A and the proposed product P, then reproduce the original ORs when needed. A stronger signal has at least the required positive bits and no extra negative bits. Removing both ordinary ANDs leaves at most eight ordinary ANDs and nineteen ORs. Every retained record must force twenty or more ORs. The data contains finite cliques, guard-false cliques and row packings; strengthened records additionally pin operand traces. HiGHS used eight seconds per negative-clique optimization, with no separate time limit per 52-flag packing. A solver's search result alone never dismisses a candidate.

Run python research/order3_case35_h19_fifth_after_first_or.py --write-frontier residual.json to replay the retained certificates against the original test columns and export both residual sets. The Lean theorem and broader 90-second CaDiCaL UNKNOWN query are documented in research/results/2026-11-28-case35-h19-fifth-gate.md.


## Verified outcome

| Branch | Remaining before new certificates | Remaining after replay | Additional two-source records |
| --- | ---: | ---: | ---: |
| Independent Y,Z | 66,828 product columns | 0 | 4,524 |
| Z reads Y, after using the independent records | 12,665 (Y,Z,P) triples on 2,973 product columns | 0 | 806 |

In the independent branch the OR floors were 20 on 142 records, 21 on 1,449 and 22 on 2,933. Twenty records used the strengthened operand-trace check. In the dependent branch the corresponding counts were 56, 235 and 515, including 23 strengthened records. All 5,330 two-source records meet the full nineteen-OR threshold. A separate exploratory three-preload trace was unnecessary for coverage and does not contribute to these totals.

There is a dependency consequence. If B is the second ordinary AND after the 17 fixed gates, it must have at least three distinct suffix OR ancestors besides X. Otherwise keep A and X first and move the predecessor closure of B forward. Besides A and the fixed X, that closure needs at most two ORs and the guard masks on its predecessor paths. Moving the other gates later preserves the circuit and the physical guard count. This places B third, fourth or fifth among non-guard operations, all excluded. If X is also an ancestor of B, at least four suffix ORs are its ancestors.

The next open order for these fixed first two operations has an ordinary AND in position six. The branch with a different first AND or first OR, other guard counts, and the unrestricted size-63 existence question remain open. The public project still lists L-meta-2625 as a conjecture at the 08:53:32 UTC snapshot. Upstream 6198d888f337ceb5d982d341eb883872ffeed3bd has the same three cuts. The desk did not issue a lease. No upstream submission, renewal or release was made.

## A sixth-gate subcase

Fix Y = OR(5,10) and then Z = OR(18,Y), with the operands unmasked. For this continuation the sixth non-guard operation must also be an OR, so the prefix starts AND followed by five ORs. Let W be the variable fifth OR. If the sixth operation were an ordinary AND, it would depend on both Z and W by the same topological reordering argument, now using the global fifth-gate exclusion. If W is independent of Z, the normalized product is W AND Z. If W reads Z, the normalized product is W AND v for an older column, Z, or W. All cases include masked operands. The counts are 2,724 independent W values and 142 reading Z, or 2,861 distinct values in their union.

Using the preceding two-source records leaves 21 (W,P) pairs on 19 products. Thirteen maximal products were tested with the same discovery budget. Three forced an OR floor of 20 and ten forced 21. A compact replay selected 120 pools from the inherited and new ledgers. It covers all 1,518 products that still require checking after deleting those already supplied by old wires or by W. The signed replacements retain the same two-AND saving as above. Run `python research/order3_case35_h19_sixth_gate.py` to verify those 120 records and repeat the enumeration. No sixth AND remains in this fixed subcase. For these four named starting operations, the next open position for an AND is the seventh non-guard operation. For general Y and Z after A and X, the sixth position remains open.
