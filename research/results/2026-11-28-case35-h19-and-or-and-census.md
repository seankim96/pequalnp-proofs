# L-meta-2625 — When a second OR depends on the first ordinary AND

Parent checkpoint cae261276db61593795c7c8008c776813a593143. Use the 17 gates PREFIX13 + POINT7 of case 35, the 52 positive and 468 negative inputs, size 63, and exactly 19 physical ANDs reading guard wire 32. In the (10 ordinary AND, 19 OR) suffix, if the first non-guard operation is an ordinary AND and the second is an OR which reads its output, the third non-guard operation must be an OR. Reading through any number of intervening guard masks is included. This extends the previous fixed OR(14,18) analysis to a structural restriction on the second OR's operands. For a first AND on wires (1,14), the same third-OR conclusion holds for every second OR, including one independent of this AND.

## Reduction to two free columns

Call the first unmasked product A, the second gate's truth column X, and the third ordinary AND's unmasked product P. A guard mask on either operand of an AND can be applied to the result. Let B be the 43 starting wires after the fixed prefix and G the guard. Physical first products therefore reduce to pair products of B and optional masks. If A is signed-dominated by a free wire (including a masked wire), eliminate that first AND. The resulting OR–AND beginning is already excluded by the parent's nine-ordinary-AND/twenty-OR bound. There are 65 distinct remaining unmasked first products. For each A enumerate all ORs of two columns from B, A and their masks. The enumeration includes 8,874 (A,X) pairs where at least one realization of X uses A or A & G. All subsequent uses depend only on the value of X, so the same exclusion applies to every realization of that value.

If the third ordinary AND ignores X and its masks, the first two products can be preloaded as in the two-initial-AND result in c97920bc. That result also covers a nested product of three starting wires. If it uses X, either it copies X up to a mask, or it has P = X & s for s in B or s = A, again up to a mask. P dominated by an old product is covered by the same two-preload result. P dominated by X or its mask can be eliminated, using only the first preloaded product. If the old fixed OR(14,18) or its mask dominates X, replace X by that stronger signal and apply the parent's fixed-OR exclusion. All dominance comparisons require more ones on positives and fewer ones on negatives. They are preserved by monotone gates and by guard masks.

For the remaining P, give the suffix **two free columns** c and d. If A and P can each be replaced by one of c, d, c & G or d & G, the remaining circuit can construct X by paying for the original OR on the replacement operands. It has at most eight ordinary ANDs and **nineteen** ORs, with arbitrarily many free guard masks. The two uses may even be supplied by the same column. A certified OR floor of 20 or more on this relaxed starting pool excludes the original order. The crucial saving is that one certificate serves every X that yielded a dominated P. The replay indexes each possible wire value by the set of certificates supplying it, then intersects the sets for A and P. An empty intersection is recorded as open.

The initial search took maximal third products under signed dominance. For the fixed product on wires (1,14), 800 distinct candidate P values reduced to 345 maximal representatives across 2,519 possible X values. Of these representatives 318 were excluded by standard density and 27 by strengthened operand traces. Rechecking all 345 gave OR floors of 20 for 87 representatives and 21 for 258. The second sweep targeted all products of a dependent OR with a possible third operand. This produced 883 representative pairs before merging with the first sweep. The unconditioned enumeration below checks coverage directly from B, independently of how discovery chose the representatives.

If an AND–OR–AND continuation survives, its middle OR must use only an initial source or its guard mask on each side. Such an OR and the required initial-source mask gates can be scheduled before the first ordinary AND by topological reordering. The pending triple count concerns this particular census and does not assert existence of a circuit.

## Trace arithmetic in Lean

PlaneComplementaryTraceBound proves the threshold inequality underlying charged-signature bounds. Let k negatives have injective signatures in each of two finite sets D and E of eight-bit words. Assigned weights on the two signatures sum to at most the number of true OR outputs on their row, and its packing width is at most one plus the number of false OR outputs. For any two thresholds t and u, the total packing width plus k(t+u) is at most k(m+1) plus the total shortfalls below t on D and below u on E, where m is the number of OR gates. The proof takes the image of each injection, sums the nonnegative shortfalls, and partitions the m outputs on each row. It permits different thresholds and domains for the complementary traces. The Python verifier now uses this bound on the repeated-source trace, whose seven-bit words have six charged bits. For all 129 possible subset sizes the maximized threshold bound agrees with summing the k smallest weights. Graph clique certificates and the enumeration of prefix orders are checked in Python.

## Reproduction and solver budgets

Run `python research/order3_case35_h19_and_or_and.py` at the checkpoint root. This checks each density or fixed-bit certificate and returns the actual unexcluded triples (A, X, P) as 520-bit columns. The parent provides the earlier single/two initial product and fixed-OR certificates. Discovery used SciPy/HiGHS with an eight-second limit per incompatible-negative clique optimization. The 52-variable flag packings had no separate wall-clock cap. Greedy fixed-fiber discovery and finite path/receiver enumerations supplied the other witnesses. Only replayed bounds were used for exclusions.

The broader exact-circuit query used the same 17-gate prefix followed immediately by AND(1,14), OR(18,43), AND(4,44), allowing at least 19 guard reads with no prescribed ordinary gate split. Pinned CaDiCaL, 90 seconds: UNKNOWN, 56 encoded rows, zero decoded candidates. This timeout provides no exclusion for that broader question.

## Complete census for this checkpoint

Two additional first-product pools, AND(3,20) and AND(9,19), were chosen because each supplies five useful first-product values by signed or guard-masked dominance. Their representative sets contained 345 and 342 products respectively. Across all sweeps the merged ledger has 1,867 distinct verified two-source records. The additional and original records were independently replayed; the final census used the complete set.

| Domain of (A,X) | Total normalized pairs | Pairs still allowing an unexcluded third AND |
| --- | ---: | ---: |
| Every useful A and every possible X | 165,204 | 30,532 |
| First product AND(1,14) | 2,519 | 0 |
| OR admits an operand A or A & G | 8,874 | 0 |

The last two domains overlap. In total 134,672 pairs exclude a third ordinary AND. Of the 8,403 OR values occurring somewhere, 7,818 are fully excluded at every applicable first product. Of the 2,449 OR values independently constructible before the first AND, 1,864 are fully excluded. Twelve of the 65 useful initial products exclude a third ordinary AND for **every** subsequent OR. Their representative original operand indices are (1,14), (3,20), (3,40), (3,41), (9,19), (9,39), (9,41), (14,26), (19,27), (20,27), (27,39), and (27,40).

The remaining 30,532 (A,X) pairs expand to 55,915 unresolved (A,X,P) triples. For a concrete next slice, AND(26,41) leaves 1,003 triples spanning 725 distinct P values. Apply the same two-preload search to its maximal uncovered P values or prepay X as a third source for a residual eighteen-OR test. A pending triple carries no SAT claim.

## Checker and project status

Pinned Lean 4.36.0 project checker verdict: ACCEPTED (check), with 1,720 constants rechecked. The exact-type import passed with propext, Quot.sound and Classical.choice. The final source uses only the needed group-action and finite-sum modules. A preliminary verifier process with a broader tactic import exited 137 without a verdict; the accepted verdict is for the final source. All 87 project definition hashes matched upstream e7a9d80db315d4af5e830db155e628245f9ca700. Single-file fork commit 6ae33fc7fa1a3cd5d2a0040b29c718878fb3dbae.

The subsequent upstream snapshot 85e78577559256adddedecf17d5ed738f7509f19 still has the three reduction files 50, 317 and 487 and no unconditional L_meta_2625 file. The desk returned no lease for this gap. There was no lease to renew or release, and project submission rules precluded an upstream PR. PRs #7762 and #8170 remain merged with accepted checks and no open review threads. The unrestricted 63-gate lower bound remains open.
