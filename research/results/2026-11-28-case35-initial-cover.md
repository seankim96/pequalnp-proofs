# L-meta-2625 · Initial covers and three case-35 first-OR exclusions

Research parent `df942bed4a75e160ac433a991a698952b6993008`. On November 28 (KST) we checked the 49 existing fork branches, all four author PRs, and upstream main at `624acb3fb2189a78719c262c1af407bd73fb3b5c`. #7762 and #8170 are merged, their checker comments say ACCEPTED, and we found no actionable review feedback. The upstream files for L-meta-2625 are reductions 50, 317 and 487. The scoped desk step said not_open and its next call issued no gap or lease. No unrestricted size-63 proof was located.

## Circuit class and exclusions

Use the exact case-35 command in the [parent checkpoint](2026-11-27-case35-incomparable-or.md). The fixed 17 physical gates are followed by 46 gates, with at least 20 ANDs reading wire 32 across the circuit. Prior bounds force 18 remaining guard ANDs, nine other (paid) ANDs and 19 ORs. Tests use all 52 positive and 468 negative rows. X,Y,Z denote the first three OR outputs after the fixed prefix. Guard masking is allowed between them. An excluded value is a semantic column on the 520 rows.

| First OR X | Second candidates | Surviving (Y,Z) pairs before new checks | Fourth-output tests, summed within triples | Paid-product certificates |
| --- | ---: | ---: | ---: | --- |
| OR(5,19) | 14 | 6 | 16,857 | 14 products using Z |
| OR(11,21) | 18 | 4 | 11,306 | 3 crossed X/Y products and 6 products using Z |
| OR(8,16) | 19 | 0 | 0 | 2 crossed X/Y products |

For X=(5,19), Y=(7,13) or (13,42), followed by Z=Y OR one of wires 11, 23 or 25. For X=(11,21), the remaining ordered pairs of gate values are ((7,13),(4,8)), ((13,42),(4,8)), and those two in reverse order. All 10 triples were checked for a paid AND before the fourth OR and for a fourth OR before the first paid AND. Non-dominated prepaid products in these triples have verified floors of 21 or 22 ORs against the budget of 19. Width-16 pivot certificates account for every fourth output. Counts can overlap across triples.

For X=(11,21), the paid products X AND Y that needed further evidence have Y=(8,15), (4,15), (8,23) and certified floors 21, 21, 22 respectively. For X=(8,16), Y=(12,18) and (12,21) both give floor 22. Each calculation supplies the product as an initial wire, retains the full 19-OR budget, and allows eight more paid gates. All other crossed products have a checked dominating replacement.

## Lean result and independent instance tests

`PlaneInitialCoverOrBudget` reconstructs a set of initial wires from any set W of circuit output wires. Fix any finite indexed positive family and one negative input. A wire's support is the set of family members it accepts when it rejects the negative, and is empty otherwise. Charge one for each OR whose output support is contained in neither operand's support. There is an initial-wire set U whose supports cover the union of W's supports, with |U| at most |W| plus the number of charged ORs. There is no singleton-packing assumption on the inputs. The Lean proof traces sets of wire indices backward across each gate, replacing its output by one parent whenever that suffices and two otherwise.

The repository's pinned Lean 4.36.0 checker returned ACCEPTED (check) and kernel-rechecked 1,743 constants using propext, Quot.sound and Classical.choice. The exact saved statement compiled separately, and all 87 definition-module digests matched upstream. The standalone file is on fork commit `10c7d2a0b83445c557d5217e4fec96a42d317dd7`.

At X=(5,19) the table shows the independent application of this necessary cover condition. After prepaying Z, 16 ORs remain. The tight rows each need 17 initial wires to cover 52 positives. After prepaying a fourth OR, only 15 ORs remain, so the enlarged pool needs a cover of at most 16 at every negative. Earlier mask operations can be reproduced by ANDs at zero OR cost once the named OR columns are supplied. The cover theorem allows those ANDs. For each proposed fourth output we freely supply its exact column.

| Y | Z | Negative row indices needing 17 wires | Fourth outputs before → after cover condition |
| --- | --- | --- | --- |
| (7,13) | Y OR 11 | 48, 53, 377 | 2841 → 78 |
| (7,13) | Y OR 23 | 197, 198, 200 | 2842 → 105 |
| (7,13) | Y OR 25 | 374, 377, 379 | 2842 → 105 |
| (13,42) | Y OR 11 | 48, 53, 377 | 2778 → 78 |
| (13,42) | Y OR 23 | 197, 198, 200 | 2777 → 105 |
| (13,42) | Y OR 25 | 374, 377, 379 | 2777 → 105 |

The exact dynamic program branches on a still-uncovered flag and enumerates the maximal eligible wires containing it. The cross-check used a separate unary cardinality CNF and pinned CaDiCaL. For all 18 tight instances, size ≤16 was UNSAT and size ≤17 was SAT. The SAT witnesses passed direct coverage and cardinality tests. Each call had a ten-second timeout. The stronger pivot and paid-product census is independently checked in Python. Only the general cover theorem was certified in Lean.

## Replay and budgets

From the repository root:

```sh
python research/order3_case35_initial_cover.py
python research/order3_case35_cover_sat.py "$(cd lean && lean --print-prefix)/bin/cadical"
python research/order3_case35_or_frontier.py 8 25
```

For constructing the fourth-output certificates we used width 16, seed 2801, up to 40 randomized packing proposals beyond the first per negative, each capped at three seconds of MILP time. Paid-product cliques used eight seconds per MILP and per-row packings used uncapped MILPs, followed by finite integer verification. Search misses give no exclusions. The cover dynamic program ran to completion. The SAT-loop budgets below exclude certificate replay and encoding. The 56 initially encoded rows comprise 52 positives and four negatives.

The cumulative verifier advanced from 119/230 excluded to 120, 121 and finally **122 excluded, 108 still open**. Each newly fixed first gate (OR(5,19), OR(11,21), OR(8,16)) separately returned **UNSAT on 56 encoded rows** with its corresponding cumulative cuts, the pinned CaDiCaL binary and a ten-second SAT-loop budget. All three tests fix only that one extra gate after the 17-gate prefix. The larger finite exclusions also cover guard-masked forms. No unrestricted 63-gate verdict follows from these results.

The next starting value examined was X=OR(8,25). For Y=OR(13,42), both Z=OR(5,18) and Z=Y OR wire 18 survived the third-OR census. With the former triple fixed and the older star-probe encoding (shared-first-OR cuts disabled), the 45-second SAT loop returned **UNKNOWN** on 56 encoded rows with zero decoded candidates. To reproduce, replace `--shared-first-ors` in the parent report's command with `--after-fifteen OR 8 25 --after-fifteen OR 13 42 --after-fifteen OR 5 18`, and set `--seconds 45`. The desk recheck issued no lease, so there was no lease to renew or release.

With all gates after the fixed 17 left free, the runs with 120, 121 and 122 cumulative exclusions each returned **UNKNOWN at 60 seconds**, on 56 encoded rows with zero decoded candidates.
