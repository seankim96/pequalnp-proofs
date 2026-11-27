# L-meta-2625 — two closed boundary searches and the 26-read frontier

Resumed from `f26f4948bfc419d00088ade7466634b24ad3992c`. On 2026-11-27 upstream was `004f2cd4b2239f07475a33ddbe1d680f9b40d41c`. The account had four closed PRs and 33 fork branches before this work. PRs #7762 and #8170 were merged, the checker comments said ACCEPTED, and there were no submitted reviews or inline review comments. The desk returned `not_open` for the unit and the scoped next request returned no assignment or lease. Upstream still had the three reductions 50, 317 and 487. No direct unrestricted 63-gate verdict was found.

## Lean lower bounds

Gate 7 in this orientation is OR(2,6), producing wire 32. The first twelve gates are OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27), OR(2,6), AND(1,24), AND(15,32), AND(25,32), AND(0,17), AND(0,23). Gate 13 in the second branch is AND(0,25). Let h count all ANDs after the first eight gates that read wire 32. Two such gates already occur in both prefixes.

| Prefix | Necessary size | Size-63 exclusion |
| --- | --- | --- |
| First 12 | ≥ 36 + h | h ≥ 28 |
| First 13 | ≥ 37 + h | h ≥ 27 |

These exclusions cover all remaining suffix wiring and all choices of output. Both searches had previously timed out. The new theorem combines independent operator lower bounds. Fix a family of 131 negatives and 28 positive flags. Every pair of these negatives admits a positive witness: every original wire true on that positive is true on at least one negative, and the guard, if true on the positive, is true on both negatives. All wires added by gates 8–13 are false on those 28 positives. Guard ANDs can be treated as free masks and ORs require no trace bit. Each remaining non-guard AND contributes at most one bit to a negative's trace. All 131 traces must differ for a separator. Seven bits distinguish only 128 rows, so the remaining suffix needs at least eight non-guard ANDs. Independently the OR-count argument requires at least 18 ORs after gate 7. Since gates 8–13 are ANDs, these 18 ORs must all be in the tail. Adding its actual guard reads gives the displayed inequalities.

The exported theorem `PlaneCase35ThirteenGateTrace` applies after **any** intervening block whose newly produced wires are false on those 28 flags. It permits intervening ORs and deducts those already spent. The certificate is self-contained. The checked corollaries `Ordinary.bound12` and `Ordinary.bound13` instantiate the two physical prefixes. An independent Lean file re-elaborated both concrete size-64 conclusions, checking 26 or 25 remaining guard reads respectively.

## All 741 non-guard ANDs on the original 39 wires

At the 13-gate prefix, h=26 is still open. The same 24-flag support test directly covers 680 of the 741 legal non-guard ANDs in slot 14. We separately tested all 741 using explicit negative families. For each AND(a,b), preload its output alongside the 39 wires and find at least 129 negative rows with pairwise witnesses for that enlarged pool. Group sizes by number of gates are 707, 16, 17 and 1. The four negative families have sizes 131, 129, 132 and 206. Each certificate separately implies at least eight non-guard ANDs even with that gate output provided as an input. The family choices and gate codes are in `research/results/case35-gate14-trace-families.json`; the code is 39*a+b for a ≤ b, neither operand 32.

The generic Lean lemma `PlanePreloadedAnd` applies this idea to every later occurrence of a given AND(a,b). Prepend its value to the wire pool, shift every other index by one and replace all occurrences of that physical conjunction (either operand order) by copies of the preloaded wire. Every output is identical on every row. If the augmented pool needs at least eight non-guard ANDs and the pair occurs m times in the original tail, the original needs at least 8+m. There are 50 tail slots, at least 18 are ORs and at least h−2 are guard reads. Hence **m+h ≤ 26** for each of these 741 physical pairs. At h=26 every later non-guard AND must read at least one wire numbered 39 or higher. At h=25 no individual fixed pair can occur twice. The 741 finite trace premises were independently replayed in Python on the physical row words. This aggregate application is a certificate-based computational reduction; the general preloading lemma and the concrete 12- and 13-gate bounds were checked in Lean.

## Reproduction and solver outcomes

Run `python research/order3_case35_thirteen_gate_trace.py`. The scalar replay checks every one of the initial 8,515 pairs on the 39 physical wires, then independently checks all four families against each assigned gate, both negative endpoints, and all eligible positive witnesses. It verifies exact coverage of all 741 physical codes. The upgraded encoder accepts `--trace-budget` for the 131-negative bound, `--gate14-trace` for the single next-gate classification, and `--preloaded-trace` for the entire tail. The latter two revalidate the finite certificates before using them.

All runs used pinned Lean 4.36.0's CaDiCaL with size 63. The CEGIS seeds were all 52 positive rows and negative indices 0, 1, 2, 234. The candidate test set contained 520 rows. Common arguments:

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --eleventh AND 0 17 --twelfth AND 0 23 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --wire-credit --adaptive-charge --trace-budget --solver "$SOLVER"
```

Use `--min-guard-reads` and `--seconds` as indicated below. All except the first also fix `--thirteenth AND 0 25`.

| Additional fixed gates / flags | Minimum guard reads | Wall limit | Actual result |
| --- | ---: | ---: | --- |
| 12 fixed; `--dominating-guard` | 28 | 10 s | UNSAT on 56 rows (solver result) |
| 13 fixed | 27 | 10 s | UNSAT on 56 rows (solver result) |
| 13 fixed | 26 | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 14 = AND(2,14) | 26 | 10 s | UNSAT on 56 rows (solver result) |
| 14 = AND(1,14) | 26 | 60 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 14 = AND(1,14); `--gate14-trace` | 26 | 10 s | UNSAT on 56 rows (solver result) |
| 13 fixed; `--gate14-trace` | 26 | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 14 = OR(36,37), 15 = AND(1,14); `--preloaded-trace` | 26 | 10 s | UNSAT on 56 rows (solver result) |
| 14 = OR(14,18), 15 = AND(1,39); `--preloaded-trace` | 26 | 60 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |
| 13 fixed; `--preloaded-trace` | 26 | 90 s | UNKNOWN, 56 encoded rows, 0 decoded candidates |

The UNSAT regressions contain a contradiction from a bound or from the replayed certificates. A timeout is UNKNOWN. Remaining search: the 13-gate prefix at h=26 with a later AND that uses a post-prefix wire, in particular the tested OR(14,18), AND(1,39) continuation. Another direction is to kernel-check the four certificate families to promote the aggregate numerical application into a single unconditional Lean statement. The unrestricted target remains open in this work.

## Verification and publication

Both one-file research contributions received **ACCEPTED (check)** from the upstream repository's pinned checker. The trace bound's manifest rechecked 2,225 constants and the preloading lemma's manifest rechecked 1,738. Independent elaboration checked each external statement and verified all 87 upstream definition-module digests against Git. The concrete bounds and both checker verdicts list only propext, Classical.choice and Quot.sound. No upstream PR was opened because the desk did not issue a unit. The fork comparisons are:

- [Trace bound](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-thirteen-gate-trace) at `6d6dc8bc98df40d39579086bb22270ddc534110e`.
- [Preloaded AND](https://github.com/open-goat/pequalnp-proofs/compare/main...seankim96:pequalnp-proofs:research/l-meta-2625-case35-preloaded-and) at `16f73f420938b662bc72d5b31a38e62646346ae6`.
