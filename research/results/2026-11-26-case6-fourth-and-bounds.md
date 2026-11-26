# L-meta-2625 — AND counts after the fourth gate

Parent checkpoint 8c6a835d9335fdfc9e4506574eefee5814e30bdc. The fixed three-gate prefix is AND(0,13), OR(0,14), AND(1,13). The 1,682 ordered fourth-gate codes encode OR and AND on pairs of the 29 available wires. All proof statements use 52 positive and 468 negative tests, arbitrary suffix length and output index, sharing, and both constants. For the 63-gate search there are 59 free slots.

## Code 858 and transfer

Code 858 is AND(0,17). The prior run found 414 compatible negatives here. The direct proof takes the first 257 from the ascending-order greedy selection and checks all 32,896 unordered pairs, the positive inputs, and the mapping to the actual 468 negatives. The separating-pair theorem forces nine suffix AND gates.

PlaneFourthAndTransfer replays any proposed suffix in the previously certified code-84 branch. First compute the desired fourth gate from wires 0–28 and append it to the 32-wire code-84 initial state. Its result occupies wire 32. Rename wire 29 to 32, keep both constants, and shift every suffix wire by one. Induction over the gate list preserves each output on every test. The simulated circuit spends zero extra AND gates for an OR and one extra AND gate for an AND. This proves at least nine suffix AND gates in all 841 OR cases and at least eight in all 841 AND cases.

## A certificate shared by 724 AND codes

Give the fourth wire an idealized column that is true on only the eight positive positions in the 52-bit mask 0x10100000100f1 and false on all negatives. Greedy selection finds 306 compatible negatives even with this column. PlaneMaskAndCount uses 257 of them. If another column's positive support lies inside this mask, replacing that column by the idealized one can only increase a circuit's positive outputs and decrease its negative outputs. A correct circuit remains correct. The same nine-AND bound therefore holds for every such column, regardless of its negative bits. The finite count of 724 qualifying ordered AND codes appears in the theorem statement.

Together these results give nine suffix AND gates for 1,565 codes and eight for the other 117. The existing uniform eighteen-OR lower bound continues to apply. The resulting total suffix bounds are 27 and 26, respectively. Neither rules out the 59 available slots.

## Solver replay

Use research/order3_prefix_search.py with --case 6 --third AND 1 13 --fourth AND 0 17 --operator-bounds and the CaDiCaL 2.1.2 executable shipped with Lean 4.36.0. Both runs start from two positive and two negative rows and check every decoded candidate on the 520-row specification.

| Checkpoint / minimum suffix AND and OR | Budget | Encoded rows at timeout | Rejected candidates | Verdict |
| --- | ---: | ---: | ---: | --- |
| Parent / 2 AND, 18 OR | 150 s | 40 | 9 | UNKNOWN |
| This session / 9 AND, 18 OR | 180 s | 36 | 9 | UNKNOWN |

## Remaining certificates

The earlier all-code numerical scan still predicts nine AND gates for the remaining 117 codes. A candidate next mask is 0x10001010121f: it covers 24 additional ordered AND codes and permits a greedy set of 270 negatives for its idealized column. The class after that is 0x8a08024088000 with 18 more codes and 277 negatives. These two masks have numerical checks only. For reproduction, use the prior scan's bitset certificate(mask, 0) on the three fixed gates, then take the first 257 set bits in increasing index order. Input row and bit numbering are zero-based. Another route for diagonal cases is to recognize that AND(i,i) and OR(i,i) are identical on every row.

The desk reported a live holder of L-meta-2625. This session did not take, renew or release that lease or submit upstream. PRs 7762 and 8170 are merged with accepted checks and no change requests.

A numerical comparison of all 520-row signatures narrows the remaining work further. Of the 117 uncovered ordered AND codes, 31 have a column identical to some OR code. The other 86 codes have only 43 distinct signatures, each true on exactly one positive row. Code 888 is the first of these 86. The SAT driver currently keeps the weaker eight-AND bound on all 117.

## Checker verdicts

The repository checker accepted all three expanded statements in check mode under Lean 4.36.0, exit 0. The kernel rechecked 1,970 constants for PlaneCode858AndCount, 2,001 for PlaneFourthAndTransfer and 1,983 for PlaneMaskAndCount. The only reported axioms were propext, Quot.sound and Classical.choice. The initial transfer checker process exited 137 without a verdict; its completed retry on the same source returned ACCEPTED.
