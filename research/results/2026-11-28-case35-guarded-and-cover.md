# L-meta-2625 · Paid-AND dependency and first-OR reductions

Research parent `cd5b4ce8666e58f911eb8fd5371b88aff14b18e5`. On November 28 KST we inspected the author's four PRs, 50 fork branches and upstream main `c45a2d13809b35f95bdf3b4ce853de2bbfb5ce6d`. PRs #7762 and #8170 are merged, with ACCEPTED checker comments and no actionable feedback. Upstream still had the three L-meta-2625 reductions 50, 317 and 487. The desk returned not_open and its scoped next requests issued no lease. No unrestricted 63-gate result was located. This checkpoint is on the fork.

Use the case-35 command and exact 17-gate prefix in the [case-35 report](2026-11-27-case35-incomparable-or.md). The circuit has 26 inputs, 52 positive rows and 468 negative rows. A guard AND reads physical wire 32. Other ANDs are called paid. The size-63 branch with at least 20 guard reads has 19 ORs, 18 guard ANDs and **nine paid ANDs** in the suffix. All row and wire indices are zero-based.

## An exact paid-AND count for an independent layer

Start from the 43 wires after the fixed prefix. Allow unlimited ORs and guard ANDs. Require that the output of a paid AND does not reach the input of any other paid AND in the suffix. The exact minimum number of paid ANDs for the 520 tests is **11**. The same minimum holds after additionally preloading X=OR(8,25), Y=OR(13,42), Z=OR(5,18). Thus any solution in the nine-paid-gate branch must pass information from a paid gate to a later paid gate.

* With only free operations, a wire is an OR of initial wires and guard-masked initial wires. This follows by distributing the guard over OR and using its idempotence. For an independent paid layer, the final output is consequently an OR of such free terms, paid products, and guard-masked paid products.
* The union of safe free wires misses 38 positives. A directly used product must reject all 468 negatives. A guard-masked product need only reject the guard-on negatives before masking. For either test, label sources on two sides. Two sources are compatible if their intersection is zero on the required negatives. Any safe product uses a complete bipartite subgraph of this relation. Extending its right side to the common neighbors of its left side and then taking all compatible left sources preserves safety and only adds accepted positives. Enumerating all intersections of source neighborhoods is therefore exhaustive for the maximal cover calculation.
* The direct and masked enumerations have 380 and 96 neighborhoods respectively. A single term covers at most four or three of the 38 positives respectively. Its hits on the eleven pivots **4, 8, 14, 18, 23, 27, 28, 32, 42, 46, 51** number at most one in both modes. None of the eleven is covered by a safe free term, so eleven paid terms are necessary.
* Across the two modes, 22 inclusion-maximal hit masks remain. An exact set-cover search selects eleven, reconstructs both operand unions for every term, and verifies that their OR with the safe free wires accepts exactly the 52 positive rows and rejects all 468 negatives. A separate saved physical witness replays the 17 fixed gates and a suffix of 11 independent paid ANDs, four guard ANDs and 45 ORs. It uses 77 gates total. This attains the paid-AND optimum with unrestricted OR/guard use; it does not improve the known 64-gate upper bound.
* A separate CNF encoding permits every subset of sources on either side. On both pools, pinned CaDiCaL returned SAT at four direct hits and UNSAT at five, and SAT at three masked hits and UNSAT at four. Asking for any two of the specified eleven pivots gave UNSAT in all four pool/mode combinations. SAT models were evaluated directly. Per-call timeout was 30 seconds.
* Repeating the exact cover calculation at the shorter prefixes from gate 7 through gate 16 gives minimum 12 throughout, then 11 at gate 17.

A stronger enumeration allows one designated paid gate to feed any number of later gates. Before this gate only guard masking may intervene after the stated pool. Enumerate every possible value of its product, supply that value as an extra initial wire, and recompute the exact independent-layer optimum for all later gates with free ORs and guard ANDs. **All 840 of 840** product values at the 43-wire pool and **all 952 of 952** at the 46-wire pool still require **11 subsequent independent paid gates**. This last conclusion fixes the boundary at which the first product is selected. If intermediate ORs before that first product are unrestricted, the smaller enumeration of raw or masked wire pairs does not cover them.

## Lean contribution

`PlaneGuardedAndCover` is a general cover theorem for a fixed positive pivot and a finite family of negative rows. A wire's support is its set of rejected family members when it accepts the pivot, and empty otherwise. Designate any finite set of initial wire indices with empty support. For any final wire set W, its support union is covered by at most |W| plus the number of ANDs which both accept the pivot and use neither designated input, using only initial-wire supports. The proof tracks a set cover backward through an arbitrary circuit DAG. At each OR one pivot-accepting parent suffices; an AND can need two, but one suffices if the other has empty support. Designated wires retain their initial columns throughout the execution. For a guard that accepts the pivot, take the family of guard-on negatives; if it rejects the pivot, all negatives can be retained.

Lean 4.36.0 project checker: ACCEPTED (check), 1,745 constants kernel-rechecked, axioms propext, Quot.sound and Classical.choice. An independent Lean import compiled the saved statement, and all 87 definition hashes matched the checked upstream commit. Single-file fork branch `research/l-meta-2625-guarded-and-cover`, commit `d36d26d89d5df15b7c3315012d86edeec60843e7`. The exact counts for concrete rows, rectangle separation and construction are independently replayed finite calculations.

## First-OR search

| First OR X | Second values | Third cases requiring a new fourth-OR certificate | Fourth outputs checked across triples | Extra prepaid products |
| --- | ---: | ---: | ---: | --- |
| (8,25) | 19 | 14 | 39,543 | 14 using Z, 2 crossed X/Y |
| (12,22) | 18 | 4 | 11,306 | 6 using Z, 3 crossed X/Y |

First pay-before-fourth and fourth-before-first-pay alternatives were checked over all 520 rows. Prepaid products are supplied without spending an OR, leaving eight paid ANDs. Certified OR floors were 21 or 22 against a budget of 19. The fourth-OR pivot search preloads the three OR outputs, leaving 16 ORs, and covers every guard-masked or unmasked fourth output in each triple. Counts are distinct within a triple. In the previously timed-out X=(8,25), Y=(13,42), Z=(5,18) triple there were 2,791 fourth outputs.

Against the same bank after those two cuts, a sweep of all 106 remaining first values found seven for which every second paid cross is dominated and no third OR survives. Each was replayed independently of the other six. The first pairs (number of second values) were (4,12) (21), (14,15) (33), (14,18) (19), (15,18) (34), (15,21) (19), (16,21) (21), and (18,23) (24).

## Reproduction and budgets

```sh
python research/order3_case35_guarded_covers.py
python research/order3_case35_flat_paid.py
python research/order3_case35_first_product.py "$(cd lean && lean --print-prefix)/bin/cadical"
python research/order3_case35_prepaid_flat.py
python research/order3_case35_or_frontier.py 4 8
```

Width-16 certificate search used seed 2901, up to 40 randomized proposals in addition to the first per negative row and three seconds per proposal MILP. Paid-product cliques used eight seconds per MILP and uncapped per-row packing MILPs, then exact finite replay. The rectangle and set-cover enumerations ran to completion. The circuit SAT-loop budgets exclude encoding and replay. All SAT rows below use 52 positives and four initially encoded negatives; the branch certificates themselves use 520 rows.

CaDiCaL returned **UNSAT** within a ten-second SAT-loop budget when fixing the first X=(8,25), when fixing the previously timed-out triple X=(8,25), Y=(13,42), Z=(5,18), and when separately fixing X=(12,22), with 123/124 cumulative first-value exclusions as applicable. The former 45-second baseline for the triple lacked these cuts. With the suffix free after the 17 gates, both corresponding 60-second runs returned **UNKNOWN**, zero decoded candidates.

For the next first value X=(4,8), the previous star-probe encoding with Y=(11,42) and Z=(13,21) returned **UNKNOWN** at 45 seconds on 56 encoded rows, zero decoded candidates. To reproduce the baseline, replace `--shared-first-ors` in the earlier report's case-35 command with `--after-fifteen OR 4 8 --after-fifteen OR 11 42 --after-fifteen OR 13 21` and set `--seconds 45`. No other session's lease was modified.

Full cumulative replay verified **131 excluded first ORs and 99 remaining** out of the initial 230, down from 108 remaining in the parent checkpoint. The seven empty-third cases checked 171 second continuations. A ten-second cut-assisted run fixing only OR(14,18) returned UNSAT on 56 encoded rows.

With all 131 exclusions and no gates fixed after the 17-gate prefix, the 60-second SAT loop returned **UNKNOWN**, 56 encoded rows and zero decoded candidates. The unrestricted 63-gate lower bound remains open in this work.
