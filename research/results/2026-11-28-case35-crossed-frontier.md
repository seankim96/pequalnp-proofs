# L-meta-2625, case 35: nineteen first-OR exclusions and a six-product witness

Parent research checkpoint 86ff3c5bfcb20e91bfc02972add4ad4668568863. The upstream snapshot for this run was 2a34b0378be24c16e49dad8701ab1821c1cf1963. It has three R_meta_2625 reductions and no L_meta_2625 proof file. The scoped desk returned not_open and issued no lease. PRs #7762 and #8170 remained merged with ACCEPTED checks, no reviews and zero inline comments.

## Finite 63-gate search

Fix case 35, the parent’s first 17 gates and h=20. The remaining budget is 19 OR gates, 18 physical guard ANDs and nine other (paid) ANDs. Every truth column in the certificate replay has 52 positive and 468 negative bits. The checks use the packing, prepaid-product and OR-reordering rules from the previous checkpoints.

1. For X=OR(4,10), replay the 21 second-OR continuations. There are 28 ordered second/third pairs, including the prior checkpoint's (13,42)/(12,14) probe. Across the 28, all 79,124 fourth-OR values are excluded by width-16 packings; distinct counts are per ordered triple. Eighteen previously undominated products using Z were checked by preloading the product alone: eight require at least 21 ORs, ten require at least 22. The remaining X/Y cross with Y=OR(14,23) has a certified floor of 21.
2. Against the bank after (4,10), seventeen further first columns have no surviving third OR. The 558 second continuations were checked independently against the same prior exclusions. Forty X/Y products needed individual certificates; supplying the product as a free initial wire still requires more than 19 ORs. No member of this group uses any other member as a premise. The first pairs are (4,15), (5,11), (7,10), (8,12), (8,15), (8,23), (10,11), (10,21), (10,22), (10,42), (12,21), (13,21), (13,23), (14,23), (15,22), (16,22) and (21,23).
3. For X=OR(10,15), the four third continuations are Y=(11,42) or (7,11) followed by Z=(13,22), and Y=(13,22) followed by either of the first two. The width-16 replay excludes 11,294 fourth values. Ten additional products involving Z have certified OR floors of 21 or 22, and the earlier crosses with Y=(11,22), (11,14), (5,22) have floors 22, 22 and 21 respectively. With only the old star-probe encoding, the (11,42)/(13,22) triple had timed out at 45 seconds on 56 encoded rows with zero decoded candidates.

Fourth-column discovery used seed 3101 for the 27 new (4,10) triples and 3111 for the four (10,15) triples, 40 randomized starts plus the initial choice per negative, 3 seconds per packing MILP. The previously saved triple uses seed 3011. Clique search allowed 8 seconds per MILP and the per-row packing search used solver defaults. Replay reads the saved witnesses and checks the inequalities directly. Candidate-generation time limits do not establish an exclusion.

## Dependent versus independent ANDs

The separate six-product circuit accepts 21/52 positives and rejects 130/468 negatives. Its correctly classified subset includes all eleven positive pivots and all ten negative rows of PlaneElevenSeparatedProducts. Thus the same 151-row subproblem admits a six-paid-AND circuit with reuse and has the previous eleven-paid-AND lower bound for an independent layer. This comparison allows unlimited ORs and physical guard reads after the prefix. A direct binary implementation of this six-product suffix, without sharing ORs, costs 53 ORs, seven distinct guard masks and six paid ANDs after the prefix. This is a construction cost; physical gate count was not minimized. The full specification has 31 missed positives and 338 falsely accepted negatives for this witness.

The existential Lean statement gives the 26 initial bit columns on all 520 rows, executes the actual 17 prefix gates, and appends each of six dependent ANDs followed by its guard-masked copy. Each operand selects only already available indices. The output is certified equal to an explicit 520-bit integer. A second evaluator starts from the original scalar inputs and checks the input columns, output integer and original pivots independently. The witness was found by deleting, adding and replacing source selectors in a previous six-gate implementation; no optimality is claimed.

The optional postfilters in the JSON file cost one extra paid AND each. Scalar replay gives positive/negative hits of 15/315, 14/293 and 13/271 at budgets seven, eight and nine respectively. The Lean file certifies the six-product witness; the optional postfilters are numerical checks.

Run from the repository root:

```sh
python research/order3_case35_six_dependent_replay.py
python research/order3_case35_or_frontier.py 11 14
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneSixDependentProducts.lean research/statements/PlaneSixDependentProducts.txt check
```

The final free-suffix SAT command uses both negative seeds and all 52 positives:

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 \
  --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives \
  --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads 20 \
  --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget --preloaded-trace --guard-read-ceiling --or-trace-density \
  --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41 \
  --star-probes --shared-first-ors --seconds 60 --solver /path/to/pinned/cadical
```

Append --after-fifteen OR a b once per fixed additional gate. The 45-second baseline trials used star probes without --shared-first-ors. Timeout is UNKNOWN.

## Lean verification

Pinned leanprover/lean4:v4.36.0 and tools/check-lean.mjs returned **ACCEPTED (check)** for PEqualNP.Research.PlaneSixDependentProducts. The kernel rechecked 1,715 constants, with propext as the only reported axiom. An independent import compiled the exact recorded statement, and all 87 definition files matched upstream 2a34b0378b byte for byte. The checked single-file contribution is fork commit c345a218e7295ff57ad98420be7a120b002e88f0. This is a witness for a restricted classification task. It neither decides the full 63-gate search nor supplies a correct circuit for the 520-row table.

## Verdicts and resumption

The cumulative replay progressed from 132/230 to 133, then 150, then 151 excluded first OR columns. **79 first columns remain** at this fixed prefix. CaDiCaL returned UNSAT with a 10-second limit on 56 encoded rows for X=(4,10), the previous run's X=(4,10)/Y=(13,42)/Z=(11,14), X=(8,12), X=(10,15), and X=(10,15)/Y=(11,42)/Z=(13,22), with the corresponding verified first-OR cuts enabled. Free-suffix trials with 133 and 150 cuts both timed out at 60 seconds, with 56 encoded rows and zero decoded candidates.

The next first OR is (11,14). At Y=(4,13), Z=(7,23) a 45-second pre-cut baseline returned UNKNOWN on 56 rows with zero decoded candidates. Resume with fourth-OR and early-product certificates for that triple. The ending desk check still returned not_open, and upstream e990d91803 still contained only the three R_meta_2625 reduction files for this assignment.

With all 151 exclusions and the suffix otherwise free after gate 17, the final 60-second solver run also returned **UNKNOWN**, 56 encoded rows and zero decoded candidates. The (11,14) frontier has 14 second continuations and four third continuations in total. The unrestricted 63-gate verdict remains open in this research.
