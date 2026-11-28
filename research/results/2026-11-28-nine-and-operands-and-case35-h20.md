# L-meta-2625 — Case 35 at twenty guard reads, and the nine-AND necessary conditions

Research parent `0d75ef3b4f527616e694fbbd9f6154825fc92154`. The unrestricted 63-gate question is still open. The desk returned no unit for this gap. No lease was acquired. The account's four upstream PRs are merged, including #7762 and #8170, both with accepted checks and no outstanding review request.

## Fixed case 35, 17-gate prefix, h = 20

Use the 52 positive and 468 negative tests in `order3_prefix_search.test_rows()`. The first 17 gates, from wire 26, are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24), AND(15,32), AND(25,32), AND(0,17), AND(0,23), AND(0,25), OR(17,19), OR(20,24), OR(39,40), AND(7,41). Let h count AND gates that read wire 32, counting each physical gate once. The earlier bounds already exclude h ≥ 21 here. At h = 20 the remaining 46 gates must comprise 18 guard-reading ANDs, nine other ANDs and 19 ORs.

**Integer-certificate verdict: no completion for this prefix at h = 20.** Of the 230 first OR values surviving the original width-19 test, the previous checkpoint excluded 191. The first batch in this run excludes 37 more, and the two final cases close all 230. The original first-OR domain included 2,449 different values, including unions using guard-masked operands. No assignments to other two-gate representatives are implied.

The first batch covers 563 second-column cases, 36 third-OR cases, 101,466 fourth-column witnesses counted separately by order, 40 paid-product certificates and 67 two-OR cross certificates. The previously unresolved order (8,13)/(21,42)/(13,18) is included. The two residual first columns are X = OR(13,42) and X = OR(7,13). The old second-OR bank and earlier first-column exclusions leave 66 and 131 values respectively. The added width-18 tests remove 46 and 111. Each leaves the same 20 possibilities Y = X OR k, with k in {0,2,3,4,5,6,8,10,11,12,14,15,16,18,19,21,22,23,24,25}.

For each of these 40 orders, a first non-guard AND before Y is excluded by the earlier one-OR argument. A first non-guard AND using Y is either dominated or fails the remaining OR budget after its unmasked product is supplied in advance. All 112 exceptional products use mode zero: none requires prepaying either OR. If the next non-guard operation is instead a third OR, it is either already excluded or fails the width-17 pivot packing. The two final certificates use the same 228 prior exclusions without depending on each other. Guard gates alone can create only old columns and their guard-masked copies. None is the target.

**CaDiCaL with all replayed cuts:** UNSAT on 56 explicitly encoded rows at solver budgets of 10 seconds for the first (8,13) and its selected triple, and 60 seconds for the free suffix. Once all first columns are excluded the encoder emits an empty clause. The decisive calculation is the replay on 520 rows. With only the first 228 exclusions, the 60-second free-suffix query still returned UNKNOWN. The direct 45-second probe for (13,42)/(12,43) without the new cuts returned UNKNOWN with zero candidates. For the same 17-gate prefix the direct free-suffix h ≥ 19 query at 90 seconds also returned UNKNOWN (56 rows, zero candidates). These timeouts supply no exclusion.

**Budgets.** The 37 intermediate ledgers use width-16 random packing seeds 3801–3837, in the order in the table below. The final width-18 seed is 3891; the width-17 seed is 3900 + k. Each packing MILP allows 3 seconds and at most one initial and 40 randomized objectives per negative. Clique MILPs allow 8 seconds. Auxiliary 52-variable packing MILPs for exceptional products have no separate time cap. The intermediate triple groups have a 240-second outer limit. Final XY discovery had a 600-second outer limit. Replay validates the integer witnesses and does not use the discovery timeouts.

| First OR | Second cases | Third cases | Fourth witnesses | Paid products | Crosses | Seed |
|---|---:|---:|---:|---:|---:|---:|
| (8,13) | 23 | 8 | 22548 | 12 | 2 | 3801 |
| (8,42) | 23 | 0 | 0 | 0 | 6 | 3802 |
| (10,13) | 25 | 0 | 0 | 0 | 2 | 3803 |
| (4,7) | 24 | 0 | 0 | 0 | 6 | 3804 |
| (4,13) | 24 | 4 | 11274 | 6 | 2 | 3805 |
| (4,42) | 24 | 0 | 0 | 0 | 6 | 3806 |
| (7,22) | 30 | 0 | 0 | 0 | 4 | 3807 |
| (13,22) | 30 | 4 | 11274 | 2 | 2 | 3808 |
| (22,42) | 30 | 0 | 0 | 0 | 4 | 3809 |
| (7,21) | 22 | 0 | 0 | 0 | 2 | 3810 |
| (21,42) | 22 | 0 | 0 | 0 | 2 | 3811 |
| (7,14) | 19 | 0 | 0 | 0 | 0 | 3812 |
| (13,14) | 19 | 8 | 22548 | 8 | 0 | 3813 |
| (14,42) | 19 | 0 | 0 | 0 | 0 | 3814 |
| (5,7) | 22 | 0 | 0 | 0 | 4 | 3815 |
| (5,13) | 22 | 12 | 33822 | 12 | 2 | 3816 |
| (5,42) | 22 | 0 | 0 | 0 | 4 | 3817 |
| (7,18) | 16 | 0 | 0 | 0 | 0 | 3818 |
| (13,18) | 16 | 0 | 0 | 0 | 0 | 3819 |
| (18,42) | 16 | 0 | 0 | 0 | 0 | 3820 |
| (7,12) | 11 | 0 | 0 | 0 | 4 | 3821 |
| (12,13) | 11 | 0 | 0 | 0 | 2 | 3822 |
| (12,42) | 11 | 0 | 0 | 0 | 4 | 3823 |
| (7,16) | 8 | 0 | 0 | 0 | 0 | 3824 |
| (13,16) | 8 | 0 | 0 | 0 | 0 | 3825 |
| (16,42) | 8 | 0 | 0 | 0 | 0 | 3826 |
| (7,15) | 10 | 0 | 0 | 0 | 2 | 3827 |
| (13,15) | 10 | 0 | 0 | 0 | 1 | 3828 |
| (15,42) | 10 | 0 | 0 | 0 | 2 | 3829 |
| (7,23) | 8 | 0 | 0 | 0 | 2 | 3830 |
| (23,42) | 8 | 0 | 0 | 0 | 2 | 3831 |
| (7,25) | 2 | 0 | 0 | 0 | 0 | 3832 |
| (13,25) | 2 | 0 | 0 | 0 | 0 | 3833 |
| (25,42) | 2 | 0 | 0 | 0 | 0 | 3834 |
| (7,11) | 2 | 0 | 0 | 0 | 0 | 3835 |
| (11,13) | 2 | 0 | 0 | 0 | 0 | 3836 |
| (11,42) | 2 | 0 | 0 | 0 | 0 | 3837 |

## Unrestricted circuits with nine distinct-input binary ANDs

`PlaneNineAndOperands` has no size, prefix, or guard restriction. Every monotone fan-in-at-most-two circuit passing the desk tests has at least nine ANDs with two distinct input indices. In the equality case all 18 operand indices are internal and pairwise distinct. On the same 468 distinct negative inputs, choosing one operand of every gate gives an injective 9-bit observation. Prescribing k of those bits leaves at most 2^(9-k) matching rows. In particular each operand has weight 212–256, operands of two different gates disagree on 212–256 rows, every joint two-bit pattern occurs at most 128 times, and every prescribed three-bit pattern at most 64 times.

The pinned project checker accepted the locally recorded theorem, rechecking 2855 constants. An independent exact-type example imports the file and checks its type against the expanded statement. The manifest's 87 project definition digests match the upstream tree `34d172e43837ef0d418b2c80d51dab06b93764ff`. The one-file fork contribution is `55701484e0a25f4b9762e8aec56cd76912deeaaa`. It is a structural lemma, not a proof of the unrestricted total-gate lower bound.

### Finite enumeration beyond the Lean theorem

An intervening OR-only network computes a union of primary inputs and already computed AND outputs. A union of three distinct primary inputs has weight at least 270 on the 468 negatives, above 256. The first AND's two operands therefore come from 208 distinct two-input unions. The false constant is allowed; the true constant has weight 468. Unary gates and repeated-input binary gates add no new values. If a distinct-input AND agrees with one operand on every negative, replacing it with that operand preserves all negative rows and can only increase positive outputs by monotonicity. Such a gate in a nine-AND candidate would contradict the already proved eight-AND impossibility. This justifies removing absorbed pairs even if their physical wires are different.

The direct calculation, without symmetries or a SAT solver, considered all 21,528 first pairs. It found 20,202 with zero possible second operand, 546 with one, 312 with seven, and 468 with seventeen. Counting distinct nonabsorbed second pairs leaves 70,200 two-AND prefixes. After each, all possible unions of zero, one or two primaries with any subset of both AND outputs failed a required three-coordinate fiber bound. **Eligible third operands: zero.** The 600-second full run finished in 23.87 seconds. A 180-second run using 78 verified permutations gave identical weighted counts. This finite exclusion is executable evidence for a ten-AND lower bound. The exhaustive enumeration and its translation from arbitrary circuits have not yet been certified in Lean.

To reduce the work for a formal proof, enumerating projective frames and dualities supplies 11,232 distinct permutations preserving incidences and every negative row. The 21,528 first pairs fall into 20 orbits. Only two representatives admit a nonabsorbed second AND: ((0,1),(3,13)) and ((0,1),(13,14)). Stabilizers reduce their second choices to 3 and 12 representatives respectively. The 15 records store their exact OR supports; index 26 denotes the first AND output in this separate normalized enumeration. A direct row-by-row count rechecked the 64 bound failure for every possible third operand in all 15 representatives.

The independently checked numerical files first landed at `043b371bd118a37e751b134488132639a142e94a`. The later upstream snapshot `a98a5106f3ae5be7ed743e04d1305b42f23a2259` still contained the same three reductions and had identical pinned definitions and checker.

## Resume

For the physical branch lower h to 19. Exactly 17 of the 46 suffix gates are then guard reads. The two remaining (regular AND, OR) budgets are (9,20) and (10,19). The existing initial-pair eight-paid floors (53 pairs at 21 ORs and 850 at 22) exclude a regular AND before the first OR in the (9,20) alternative. A width-20 discovery run at seed 3919 with 40 randomized objectives found no width-20 packing and supplied no further exclusion. For the unrestricted nine-AND route the next formal gap is to certify the OR-support normal form, absorbed-gate bypass, and the 20/15 frame representative calculation in Lean.

On the subfamily of 230 original first columns, an initial replay excluded every regular AND before the second OR for 227. The other three each left one product. These counts do not cover the other first columns at the 20-OR budget. The refinement below used an eight-second clique MILP limit, and tested whether the verified floor strictly exceeds the applicable OR budget. An equal floor leaves the product open. A zero in the initial preloaded-OR column means the previous bank contains no certificate for that choice.

```text
Initial operand pairs by OR floor after removing one ordinary AND: {21: 53, 22: 850}
First OR, open (operand, AND-only floor, OR-plus-AND floor): (21, 22) [(9, 20, 0)]
First OR, open (operand, AND-only floor, OR-plus-AND floor): (14, 18) [(1, 19, 19)]
First OR, open (operand, AND-only floor, OR-plus-AND floor): (4, 5) [(17, 20, 0)]
First columns by unresolved regular-AND operand count: {0: 227, 1: 3}
first 21 22 ordinary AND with 9 prepaid first OR 0 verified floor 21 budget 20
first 14 18 ordinary AND with 1 prepaid first OR 0 verified floor 19 budget 20
first 14 18 ordinary AND with 1 prepaid first OR 1 verified floor 19 budget 19
first 4 5 ordinary AND with 17 prepaid first OR 0 verified floor 21 budget 20
newly excluded 2
```

The two strict floor-21 refinements now give 229 of 230 columns in this subfamily for which the next non-guard operation must be another OR. The unresolved exceptional order is OR(14,18), followed by AND(1,43). Its first-OR-prepaid floor equals the residual budget of 19. A broader direct h ≥ 19 search with this fixed order, no exact suffix operator split, and a 45-second solver budget returned UNKNOWN on 56 encoded rows with zero candidates. Both the (9,20) budget as a whole and the separate (10,19) budget remain open.

Reproduce from the research checkout:

```sh
python research/order3_nine_and_operands.py
python research/order3_nine_and_operands.py --symmetry
python research/order3_nine_and_frames.py
python research/order3_case35_h19_paid.py
python -c 'import sys; sys.path.insert(0,"research"); from order3_case35_or_frontier import latest_exclusions; from order3_case35_point_seven_shared_unions import *; from order3_case35_point_seven_paired import exclusions; from order3_prefix_search import test_rows; w=tuple(columns(PREFIX13+POINT7,test_rows())); print(len(first_survivors(w)-latest_exclusions(w)-proved(w)-cross_bank_exclusions(w)-exclusions(w)-{exclude_two_three(w)}))'
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneNineAndOperands.lean research/statements/PlaneNineAndOperands.txt check
```
