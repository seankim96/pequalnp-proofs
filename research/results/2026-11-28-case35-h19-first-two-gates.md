# L-meta-2625 — The first two non-guard gates in case 35 at h=19

Research parent b040526275aac680f555016df445dca44a84e621. Upstream e28038f04bea88084f1ee103fbeebda4df623da3 still has reductions 50, 317 and 487 and no unconditional L_meta_2625 file. The project desk did not issue a lease for this gap. No lease was renewed or released, and no upstream submission was made. PRs #7762 and #8170 are merged, both with accepted checks and no outstanding review threads.

## Branch covered

Use case 35's 17-gate prefix PREFIX13 + POINT7 on the 52 positive and 468 negative inputs. From wire 26 onward the gates are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24), AND(15,32), AND(25,32), AND(0,17), AND(0,23), AND(0,25), OR(17,19), OR(20,24), OR(39,40), AND(7,41). Fix exactly 19 physical AND gates reading guard wire 32 in the 63-gate circuit, leaving 17 guard ANDs in the 46-gate suffix. Non-guard gate order ignores any intervening guard ANDs.

**With nine ordinary ANDs and twenty ORs in the suffix, the first two non-guard gates must both be ORs.** This covers all 2,449 distinct possible first-OR truth columns, including guard-masked operands. The parent's 1,212-column search was deeper in one particular OR-then-AND order after the 17-gate prefix. This result excludes that entire order and all its descendants. Neither the fixed case at h=19 nor the unrestricted 63-gate question is settled by this result.

## Coverage and budget

The old initial-product census already excludes an ordinary AND before the first OR in the (9,20) split. Let X be the first OR. If the next non-guard operation is an ordinary AND, its operands are old sources, X, or guard-masked versions of these. An old-old product is excluded by the same census: prepaying it lets the circuit reconstruct X normally. The other products reduce to X AND s for an old source s or to a copy of X, with an optional final guard mask. The relaxed check allows arbitrarily many guard masks. A supplied column that has more positive ones and fewer negative ones may replace a required column throughout a monotone suffix.

Scanning the starting pool and every X gave 39,928 distinct X AND s columns. Old starting and product columns or their masks dominated all but 866. These 866 have 359 maximal representatives under signed dominance. Prepaying a product leaves eight ordinary ANDs and twenty ORs; X is still charged. The first pass excluded 354 of 359 representatives at this budget. A second pass checked nine additional actual product columns, all nine with a strict floor. Five orders still needed checking with X prepaid as well, leaving nineteen ORs. Four were excluded by the existing eight-probe floor and the last by the strengthened argument below. The complete ledger uses 367 ordinary density certificates and one fixed-bit certificate. Replay covers all values, independently of the representative selection used for discovery.

## Why OR(14,18), AND(1,43) is impossible

Give both new wires to the residual circuit and remove any starting source dominated by another source or its guard mask, preserving the guard index. The remaining budget is eight ordinary ANDs and nineteen ORs. Each ordinary AND contributes one independently chosen operand observation. On a clique of incompatible negatives, these eight observations must distinguish every negative, for every orientation of the eight operand pairs. A source that is constant on more than 128 clique rows cannot serve as a probe. On the guard-false clique, at most one receiver can take a guard-masked source, so at most two such operand ports are possible.

The new ledger reuses a 132-negative clique with total positive-flag packing width 2,182. A negative with packing width f needs at least f−1 false OR outputs. The old true-entry estimate yielded an OR floor of 19. To strengthen it, suppose five exceptional operand ports (starting sources or guard outputs) could be used instead of OR or earlier ordinary-AND outputs. Partition the five ports by receiving gate into singleton and paired blocks. Distinct selected ports of the same physical source at different receivers would force duplicate selected bits; a repeated input at the same receiver is a removable copy. Previously verified constant-pair incompatibilities leave 464 five-port subsets worth testing among 34 candidate ports.

For each surviving partition the verifier finds a subset of s ports at distinct receivers, constant simultaneously on more than 2^(8−s) pairwise incompatible negatives. Their remaining bits cannot distinguish that many rows. Every partition fails. All 120 stored additional families are checked pairwise, including the requirement that synthetic guard ports vanish on each of their rows. Hence at most four exceptional ports occur.

Orient the two complementary traces so that each gets at most two exceptional ports. A probe drawn from an earlier ordinary AND implies the bit selected at that parent. These implication edges form a matching on a clique larger than 128: two receivers cannot select the same earlier output; a two-edge chain admits at most 128 signatures, and three disjoint implications admit only 108. Charge true bits of the roots other than the two possibly exceptional roots. Enumerating all 256 words and taking the 132 lightest permitted root weights yields 276, 258 and 243 for zero, one and two implications. The two orientations together cost at least 486 true OR entries because the OR sources used at different operand ports are distinct. The OR floor is therefore ceil((2182 + 486)/132) − 1 = **20**, exceeding nineteen.

At the specific deeper prefix OR(4,44), OR(8,45), OR(5,10), a direct pinned CaDiCaL run with at least 19 guard reads and no fixed ordinary-operator split returned **UNKNOWN** in 60 seconds, on 56 encoded rows with zero decoded candidates. The 520-row exclusion above uses the exact (9,20) split. The timeout contributes no exclusion to the broader query.

## Formal result

**PlanePivotalSource** is a general theorem about a size-minimum monotone fan-in-at-most-two circuit separating arbitrary positive and negative families at a fixed input width. For each gate and each earlier wire there is a labelled input on which forcing the gate to false makes the output false and forcing it to true makes the output true. On this same input either the label is positive and the gate is true while the earlier source is false, or the label is negative and the gate is false while the source is true. Thus plain inequality of the wire columns is strengthened to a signed difference on an input where the suffix is sensitive to the gate. If no such row exists, copying the earlier wire preserves separation and deleting the copy gives a smaller separator.

The pinned Lean 4.36.0 project checker accepted the theorem and rechecked 1,743 constants. Its 87 definition hashes match the upstream snapshot. An independent exact-type import compiled. The reported axioms are propext, Classical.choice and Quot.sound. The one-file fork commit is 36b0f91ed85156bb6ee1ede374fc163223f775db on research/l-meta-2625-pivotal-source. The numerical coverage above is independently replayed in Python; the pivotal-source theorem has its own Lean proof.

Discovery used SciPy/HiGHS with an eight-second limit per negative-clique optimization. Individual 52-variable flag-packing optimizations had no separate time cap. Fixed-bit clique discovery was greedy, with no SAT or MILP used for the five-port partitions or the eight-bit weight enumeration. Only integer witnesses passing replay enter the verdicts.

## Ten ordinary ANDs and nineteen ORs

In the other remaining h=19 split, the first two non-guard gates cannot both be ordinary ANDs. Between them guard gates may introduce masks, all of which are free in the relaxation. Before any OR, the first ordinary AND is a pair product of old columns up to a guard mask. The next ordinary AND is either another pair product or a product of up to three initial columns, again up to a mask. Of 3,102 distinct triple columns, each is dominated by a free source, a maximal pair product, or a guard-masked version of one. The 65 pair columns not already dominated by free sources have 40 maximal representatives. This reduces the residual problem to at most two such representatives supplied for free. The unchanged starting pool and singly preloaded pools are covered by the older census. For two distinct representatives the residual budget is eight ordinary ANDs and nineteen ORs.

Independent replay excluded all 780 distinct pairs. Standard certificates gave OR floors of 20 for 23 pairs, 21 for 586, and 22 for 170. The pair of products on wires (1,14) and (1,18) reached only 19 with the standard bound. It has a 132-negative clique of total packing width 2,257. A 96-family fixed-bit certificate bounds exceptional ports by four and raises the floor to 20. The 780 cases thus leave no surviving pair. Across both h=19 budget splits, at least one of the first two non-guard gates must be an OR.

## Next search frontier

For the (10,19) split, additionally fix a first ordinary AND, followed by the specific unmasked initial-source OR on wires 14 and 18, and consider a third non-guard gate that is an ordinary AND. If it reads the fixed OR with an available source, its extra product can be preloaded together with the first product and the fixed OR. This leaves eight ordinary ANDs and eighteen ORs. After old-product and guard-mask dominance there are 80 additional pairs of preload values to check. Integer certificates exclude 43: three require at least 19 ORs, 34 require at least 20, and six require at least 21. Of the remaining 37, eleven gave floor 18 in discovery and 26 gave no usable floor. This partial search leaves the overall AND–OR(14,18)–AND pattern open. The replay function returns the exact set of 37 (first product, extra product) bit-column pairs for resumption. A candidate still in this set is not a circuit witness.

Reproduce from the checkout root with Python and the research dependencies:

```sh
python research/order3_case35_h19_exceptional_floor.py
python research/order3_case35_h19_first_or.py
python research/order3_case35_h19_two_initial_ands.py
python research/order3_case35_h19_fixed_second_or.py
```

Before publishing, upstream was checked again at 3ebf5dd81032071db2ca88a77d7437cb92909272. The same three L-meta-2625 reduction files are present and the 87 checker definition digests still match.
