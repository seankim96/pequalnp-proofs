# L-meta-2625 — a charge count that follows the constructed wires

Checkpoint parent `19707e4087359b99a1a82af5182694b5b598bdcb`. Upstream `8f68ddc158ee34bf64ba8bdcbf0b2d635b20e79e`. On 2026-11-27 the desk returned `not_open` for this unit and no assignment from the scoped next request. No lease was obtained. Upstream contained reductions 50, 317 and 487 and no direct proof file. All four account PRs were closed. #7762 and #8170 were merged with accepted checks, no submitted reviews or inline review comments. The fork had 32 branches before this checkpoint.

## Checked mathematical content

Start Case 35 with OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24). For each later gate, examine the wire pool **immediately before that gate**. Give the gate one unit of weight if an idempotent gate (a copy) or an AND reading wire 32 can replace it, such that the new truth column contains all its positives and introduces no negative that was previously false. A gate gets at most one unit. All explicit guard ANDs get one. No minimum guard count is needed for the lemma.

For any separator of the 52 positive and 468 negative rows, **size ≥ 35 + total weight**. The proof constructs a new circuit of equal length. At each step it picks a replacement using the original pool and applies its wiring to the improved pool. Row-wise monotonicity propagates through this second change. The chosen replacement has semantic credit in *every* pool, making its contribution stable under all previous edits. The unchanged option handles an uncharged gate. Applying the existing semantic-reuse bound to the constructed separator gives the inequality.

The theorem in the one-file branch takes the existing semantic-reuse inequality as a hypothesis; its composition with the already checked `PlaneCase35SemanticReuse` was independently compiled. `fourteenBound` additionally proves a concrete 64-gate lower bound in Lean. Extend the eight fixed gates by AND(15,32), AND(25,32), AND(0,17), AND(0,23), AND(23,26), AND(0,38). Wire 37 can replace either of the last two gates. The file proves the positive implication for all 52 rows and silence of wire 37 on all 468 negatives. Two initial guard ANDs plus the two replacements supply four charges. If at least 25 ANDs in the remaining tail read wire 32, size is at least 35 + 4 + 25 = 64. Equivalently the required total guard count after the first eight is at least 27 here. The fully composed corollary takes only the output separation and tail guard-count hypotheses.

## Numerical coverage of the previously unresolved twelve-gate prefix

Keep the first twelve gates in the list above. Enumerate physical binary gates, treating the two operand orders as identical and permitting repeated operands. Count gate 14 in its own pool, including the output of gate 13. Run `python research/order3_case35_adaptive_charge.py`.

- Of 1,482 possible thirteenth gates, 722 non-guard gates earn weight. At h=28 this excludes one additional gate beyond the earlier rules, AND(23,26), leaving 760.
- At h≥27 a size-63 separator has capacity for at most one charged non-guard gate. Of 2,311,920 ordered gate-13/gate-14 pairs, **571,276** earn two such charges. An independent replay counted the same total by grouping identical truth columns and testing set inclusion after flipping the negative-row bits.
- Of the 571,276 pairs, 450,414 pass both of the earlier individual pair tests: the two physical gates are not both semantically interchangeable in their respective original pools and are not both members of the fixed eleven-type table. This comparison only concerns those two tests. Some pairs can also be removed by other reasoning.
- For all 571,276 pairs, the second gate has a replacement using only the wires present after gate 12. Gate 14 may still *read* the new wire 38. The replay independently tests the original witness set against every second truth column. This observation suggests a smaller solver encoding: after a chargeable gate, its new value is dominated by either an old wire or its guard mask, and masking that witness again still gives an old guard mask.
- The aggregate counts are numerical instantiations of the general Lean inequality. The specific AND(23,26), AND(0,38) pair has a separate Lean certificate.

## Solver replay

Use the pinned Lean 4.36.0 toolchain's CaDiCaL. Common command:

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --adaptive-charge --solver "$SOLVER"
```

For the first three rows also add `--ninth AND 15 32 --tenth AND 25 32 --eleventh AND 0 17 --twelfth AND 0 23 --wire-credit`. All runs encoded 52 positive and four negative seeds, and would check each decoded candidate on all 520 rows.

| Additional arguments | Variables / clauses | Time budget | Outcome |
| --- | ---: | ---: | --- |
| `--min-guard-reads 28 --dominating-guard --thirteenth AND 23 26 --seconds 10` | 18,900 / 591,537 | 10 s | UNSAT |
| `--min-guard-reads 27 --thirteenth AND 23 26 --fourteenth AND 0 38 --seconds 10` | 18,375 / 508,094 | 10 s | UNSAT |
| `--min-guard-reads 28 --dominating-guard --thirteenth AND 0 25 --seconds 60` | 20,150 / 666,737 | 60 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| `--semantic-budget --normalize-guard --seconds 60` (only eight gates fixed) | 22,660 / 701,312 | 60 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |

The two UNSAT replays include the contradiction derived from the certified full-row inequality. The unrestricted 63-gate question remains unresolved. For continuation, the branch ending in AND(0,25) at gate 13 is still open. The current encoder charges only those free gates whose witnesses can already be certified using the last fixed pool. The Lean theorem also permits witnesses built later in the free suffix.

## Verification and contribution

Pinned repository checker `tools/check-lean.mjs` returned **ACCEPTED (check)** for `PlaneCase35AdaptiveCharge`, kernel re-checking 1,860 constants. The manifest lists this file and 87 unchanged definition modules verified against the upstream Git objects. The independently elaborated external statement and the fully composed concrete theorem both compiled. The concrete theorem's axiom audit listed propext, Classical.choice and Quot.sound. Local verification covers the research theorem; the desk issued no lease and no upstream PR was opened.

[One-file comparison](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-adaptive-charge), commit `70cbd81694e8aeb43d7c5b8ea4f3e8d192579dce`.
