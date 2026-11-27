# L-meta-2625 — contracting an earlier wire and charging repeated gate types

Resumed from research checkpoint `8ee464ed4c0ab641eeadb14d8abdad49386d2ebd`. Upstream was `3a0048e58ba686e3914626c39e361d47269578e9`. Before publication the fork had 30 branches and all four upstream PRs from this account were closed. #7762 and #8170 had been merged, with accepted checker comments, no review requests visible in their reviews, and no inline review comments. The desk returned `not_open` for L-meta-2625 and no scoped assignment. No lease was acquired. Upstream had reductions 50, 317 and 487 and no direct proof file for this unit. The unrestricted 63-gate question remains unresolved in this work.

## Two checked lemmas

1. `PlaneWireContraction` gives an explicit deletion map. Suppose an earlier wire is true whenever the candidate gate is true on positives, and false whenever the candidate gate is false on negatives. Delete the gate, redirect its fanout and the output, and shift every later wire number down one. This preserves suffix legality, improves every output on the appropriate rows, and shortens the circuit by exactly one. The count of suffix ANDs reading each pre-existing wire cannot decrease.
2. `PlaneCase35WireCredit` proves a bound on *all* occurrences of the following eleven unordered gate types after the fixed eight gates. Both operand orders are in the Lean certificate. The fixed gates, in order, are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24).

| Replacement wire | Gates |
| --- | --- |
| 0 | OR(0,29) |
| 3 | OR(3,28) |
| 30 | AND(0,13), AND(0,30), AND(1,13), AND(1,30) |
| 31 | AND(3,13), AND(3,31), AND(9,13), AND(9,31) |
| 33 | AND(24,26) |

Let h count suffix ANDs reading wire 32 and m count suffix occurrences in this table. These sets are disjoint; repeated occurrences count separately. The bound is **size ≥ 35 + h + m**. At size 63, h=28 forbids every listed gate and h=27 permits at most one. For this simultaneous count the proof replaces each marked gate by an OR that copies its replacement wire, preserving indices and improving separation through every subsequent monotone gate. It applies the semantic-reuse size theorem to the translated circuit. The standalone one-file theorem exposes that prior bound as a hypothesis. Its composition with `PlaneCase35SemanticReuse` was typechecked against the full unconditional size statement with just separation as hypotheses.

Pinned Lean 4.36.0, repository `tools/check-lean.mjs` in `check` mode: both verdicts **ACCEPTED (check)**. Kernel counts were 1,754 constants for contraction and 1,861 for wire credit. Each manifest contained the single research module and 87 definition modules whose SHA-256 digests matched upstream. Both external statements also typechecked independently. Axiom audits, including the composed result, listed only propext, Classical.choice and Quot.sound. The one-file comparison branches were fetched and byte-checked against these exact sources:

- [Contraction](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-wire-contraction) — e2828514d04235a13967cd3d3e4d3a362e7e0aa1
- [Wire credit](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-wire-credit) — 04b10f1664af181a3f9e6f23b44488683602e643

## Numerical replay at h=28

Run `python research/order3_case35_wire_credit.py`. It checks every replacement on 52 positive and 468 negative labeled rows. Fix gates 9 and 10 to AND(15,32), AND(25,32). Of 1,332 possible gate-11 codes, old exclusions removed 625; the new bound removes another 11, leaving 696. With gate 11 fixed to AND(0,17), the respective figures at gate 12 are 1,406 total, 668 old exclusions and 11 more, leaving 727.

The script additionally groups surviving candidates by operator and explicit guard charge and checks row-wise dominance against a retained representative. The resulting 655 and 654 representatives respectively suffice to search for existence at those immediate positions. That grouping is a numerical search simplification. It does not exclude circuits using the discarded representatives, and it was not installed as a solver constraint.

## Solver runs

All four runs used the pinned CaDiCaL, size 63, arbitrary legal binary suffix wiring, the 52 positive rows and negative seeds 0, 1, 2, 234. A candidate would be checked on all 520 rows. Common command (set SOLVER to the pinned toolchain's bin/cadical):

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --wire-credit --solver "$SOLVER"
```

For the first three rows add `--ninth AND 15 32 --tenth AND 25 32`. Append the remaining arguments shown below.

| Additional arguments | Variables / clauses | Wall budget | Actual verdict |
| --- | ---: | ---: | --- |
| `--eleventh AND 0 17 --twelfth AND 0 13 --min-guard-reads 28 --dominating-guard --seconds 15` | 18,054 / 595,894 | 15 s | UNSAT, 56 encoded rows |
| `--eleventh AND 0 13 --twelfth OR 0 29 --min-guard-reads 27 --seconds 15` | 18,054 / 525,820 | 15 s | UNSAT, 56 encoded rows |
| `--eleventh AND 0 17 --twelfth AND 0 23 --min-guard-reads 28 --dominating-guard --seconds 120` | 19,380 / 599,413 | 120 s | UNKNOWN, 56 encoded rows, zero decoded candidates |
| `--semantic-budget --normalize-guard --seconds 120` (only eight fixed) | 21,120 / 641,526 | 120 s | UNKNOWN, 56 encoded rows, zero decoded candidates |

The two UNSAT inputs contained an empty clause derived from the full-row Lean inequality and fixed charges. These are regression replays of the theorem's consequence. The two timeouts establish no impossibility.

Next unresolved branch: gate 11 AND(0,17), gate 12 AND(0,23), h=28. This candidate survives even the new representative test. A useful next reduction would fix both gates and compare the remaining gate-13 outputs on all labeled rows, or certify a tighter lower bound for this prefix before spending another identical SAT budget. The general eight-gate prefix with h free is also open. No upstream PR or lease action was taken for these fork research lemmas.
