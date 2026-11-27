# L-meta-2625 · Two first-OR exclusions and a Lean OR-counting lemma

Parent research checkpoint `97ea31839a603e2a64550331061aeaada964e348`. Examined upstream `624acb3fb2189a78719c262c1af407bd73fb3b5c`, the author's four PRs and all 48 pre-existing fork branches. PRs #7762 and #8170 were merged and had no actionable review. The desk returned `not_open` for this ID, and its scoped next request issued no lease. The three upstream files for this ID are reductions 50, 317 and 487. No unrestricted size-63 verdict was located.

## Fixed instance

Use the preceding report's zero-based case 35, the 17-gate prefix below, 26 original inputs, all 52 positive and 468 negative rows, and the restriction of at least 20 ANDs reading physical wire 32. Earlier checks force exactly 20 such gates. The 46 remaining slots have 19 ORs, 18 ANDs reading the guard, and nine other ANDs (called paid ANDs). Before a paid AND, interleaved guard ANDs can give any available wire its guard-masked copy. In the tables X, Y and Z denote the first, second and third OR outputs. Counts refer to distinct 520-bit values, separately within each triple.

## Complete finite checks

For X = OR(4,5), the previous checkpoint left 17 possible Y values. For X = OR(4,14), after the preceding cut there are 15. Every crossed paid product X AND Y has a dominating replacement in the replay. The established first-OR relocation and initial, one-OR and two-OR product tests still apply. The table lists every triple surviving the third-OR filters. Wire 44 is Y in this numbering.

| X | Y | Z | Number of triples | Fourth outputs per triple |
| --- | --- | --- | ---: | ---: |
| (4,5) | (10,13) | (7,22) | 1 | 2861 |
| (4,5) | (10,13) | (22,42) | 1 | 2792 |
| (4,5) | (7,13) | Y OR wire 8, 10, 11 or 12 | 4 | 2850 |
| (4,5) | (13,42) | Y OR wire 8, 10, 11 or 12 | 4 | 2787 |
| (4,14) | (10,13) | (7,22) | 1 | 2861 |
| (4,14) | (10,13) | (22,42) | 1 | 2792 |
| (4,14) | (7,13) or (16,23) | (16,23) or (7,13), respectively | 2 | 2860 |
| (4,14) | (13,42) or (16,23) | (16,23) or (13,42), respectively | 2 | 2791 |

If a paid AND comes before the fourth OR, its underlying product either has a checked replacement or is covered by one of 26 prepaid-product certificates. Each certificate supplies the product while retaining the three ORs in the 19-OR budget and leaving eight paid gates. The certified OR floor is 21 or 22. If an OR comes first, prepay X, Y and Z, leaving a 16-OR budget including the fourth OR. For every fourth output the integer replay checks its stored width-16 packing and pivot witnesses. The ten X=(4,5) triples comprise 28,201 output checks and the six X=(4,14) triples comprise 16,955. Overlap between triples is allowed. The checker reconstructs both the outstanding paid products and the entire fourth-output domain and requires exact coverage.

## Lean result

`PlaneIncomparableOrBudget` applies to a finite indexed family of m positive inputs and one negative input t. Suppose every initial wire that is false on t covers at most one family member. A circuit accepting all m and rejecting t has at least m−1 ORs that are false on t and whose operands each cover a family member missed by the other. Any number of ANDs is allowed. The proof bounds the union of the flag supports of an arbitrary set of wires by the size of that set plus the accumulated number of these ORs. Appending an AND or an OR with one covering parent preserves the bound at zero cost.

Pinned Lean 4.36.0 project checker: ACCEPTED (check), 1743 constants kernel-rechecked, axioms propext, Quot.sound and Classical.choice. A separate Lean import compiled the exact saved statement, and all 87 definition-module digests matched the upstream revision. The single-file branch `research/l-meta-2625-incomparable-or-budget` is at `02dd0a0a37bbad6f537355172ba7cd2abea5f8b9`. The Lean theorem is general. Specialization to the 520 rows and the larger branch census were checked by the finite replay scripts.

At X=(4,5), Y=(10,13), Z=(7,22), five distinct negative rows admit width-17 packings with only 16 ORs remaining. Thus every suffix OR must count on each such packing. The fourth-OR candidates number 2861 before filtering and 992 after forcing silence on all five negatives. The incomparable-support requirement reduces these to 163 outputs using one packing per row and to 45 using twelve packings on those same five rows. At least one operand representation must pass every packing simultaneously. The independent pivot replay excludes all 2861, including those 45.

## Reproduction and budgets

Run from the repository root. The frontier query validates all earlier cuts on this prefix; a fresh process may need several minutes. Use the bundled CaDiCaL binary of the pinned toolchain for the SAT run.

```sh
python research/order3_case35_incomparable_or.py
python research/order3_case35_or_frontier.py 5 19
```

Width-16 packing search used seed 2701, up to 40 randomized proposals after the first proposal per negative, with a three-second MILP cap each. Cross-product search used up to eight seconds per clique MILP and uncapped row-packing MILPs; only validated witnesses are consumed. The first width-17 search used one proposal per negative with a three-second MILP cap. The targeted pass tried 113 MILPs with a 0.8-second cap and added seven exact packings. No search miss or timeout establishes a lower bound.

The SAT command below leaves the suffix free after the 17-gate prefix. Insert more `--after-fifteen OP i j` arguments to fix subsequent gates. The 56 initially encoded rows are the 52 positives and four negatives. Certification uses all 520 rows. Cut-assisted SAT results depend on the checked exclusions. Solver budgets exclude setup and replay.

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads 20  --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget  --preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41 --star-probes --shared-first-ors --seconds 60 --solver "$(cd lean && lean --print-prefix)/bin/cadical"
```

The focused run with X=(4,5) and the run with X=(4,5), Y=(10,13), Z=(7,22) each returned **UNSAT on 56 encoded rows** with a ten-second SAT-loop budget and 118 checked initial exclusions. With the suffix free after the 17-gate prefix, the same cuts returned **UNKNOWN** at 60 seconds, with zero decoded candidates.

For the next first OR, X=(5,19), the cumulative verifier found fourteen second outputs. Both Y=(7,13) and Y=(13,42) left three possible third values, each formed as Y OR wire 11, 23 or 25. The X/Y paid crosses had dominating replacements. The older star-probe SAT encoding (shared-first-OR cuts disabled) with X=(5,19), Y=(7,13), Z=Y OR wire 23 returned **UNKNOWN** at 45 seconds on 56 encoded rows with zero decoded candidates. This gives a concrete starting point for the next search.

Replaying both complete ledgers gives **119 excluded and 111 remaining** of the original 230 first outputs, down from 113 remaining at the parent checkpoint. On the fixed X=(4,14) branch the same pinned solver took a ten-second budget with the older 118 cuts and returned UNKNOWN. With the 119th checked cut installed through the normal encoder it returned UNSAT on 56 encoded rows within a ten-second budget. The per-branch exclusions, the generic Lean theorem and the SAT outcomes have separate verification scopes.

With all 119 cuts and the suffix free after the fixed prefix, CaDiCaL returned **UNKNOWN** on 56 encoded rows at 60 seconds, with zero decoded candidates. The unrestricted 63-gate instance remains unresolved in this work. The desk recheck issued no lease, so there was no lease to renew or release.
