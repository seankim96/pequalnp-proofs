# L-meta-2625, case 35 — rescuing the 257th negative row

Previous checkpoint 333b02b80b86eb50081ec60f356155647e937915. Checked upstream ec5c3b478f6e7f802dae6582b0feae5cf1a378c1 with its pinned Lean 4.36.0 toolchain. At this revision the three outside files for this unit were reductions 50, 317 and 487. The desk reported not_open and issued no lease. The four account PRs were closed and the fork had 24 branches before this session. PRs 7762 and 8170 were merged with accepted checker comments and no outstanding reviews. No unrestricted solution was identified.

Gate and row conventions are those of the parent checkpoint. The six-gate prefix is OR(0,1), OR(3,9), AND(15,27), AND(17,26), AND(13,26), AND(13,27). The guard is OR(2,6). For a pair of negative rows the witness must be a positive with index at least 4, different from the omitted flag. Its active baseline wires must all transfer to the union of the pair, and if the guard is active it must transfer to both endpoints.

## Proofs

For omitted flag 44 the previous greedy construction retained 256 rows. We found 257 and checked every one of the 32,896 pairs, comparing the certificate to the exact complement bitmask in the Lean source. Eight charged AND gates give only 256 transcripts.

PlaneCase35RescuedGuardSuffix gives nine charged ANDs even if the output of each gate can be freely masked by OR(2,6). Additional initial columns are allowed: whenever such a column is active on a permitted witness, some active baseline wire must imply the column on every negative. In particular arbitrary columns silent on the permitted witnesses qualify. The physical wire AND(1,24) is active only at positive 44.

PlaneCase35RescuedGuardSize fixes gate 7 to OR(2,6) and gate 8 to AND(1,24). Let h count the ANDs after gate 8 having wire 32 as either operand, counting a gate once. Any ordinary circuit with this prefix separating all 520 rows has size at least **35+h**. Each such AND can be represented by a masked OR(x,x). At least nine other ANDs and eighteen ORs remain after gate eight. The size bound excludes the entire h ≥ 29 subfamily at size 63. Gates after the eighth can read any earlier output, and the result allows an arbitrary output index.

## Independent complete sweep for this guard

For every omitted flag from 4 to 51, two integer programs using HiGHS via SciPy searched for (a) a compatible negative family and (b) a covering by incompatible cliques. Each program had a three-second solving limit per instance. The selected cliques were made disjoint. For all 48 instances the independently checked family and partition have matching sizes; the optimization status is unnecessary for the cardinality conclusion. Each partition gives an upper bound because any compatible family can use at most one row in each class.

With omission 26 the maximum was 253; with omission 28 it was 254. The other 46 maxima were at least 257, with a maximum of 275. Omission 44 has maximum exactly 257. The 48 exact counts were checked by Python; the Lean circuit theorems above use the flag-44 lower certificate. Replay with `python research/order3_case35_rescued_guard.py`. All certificates are in `research/results/case35-guard-2-6-all-omissions.json`.

## 63-gate solver run

We additionally fixed gate 9 to AND(15,32) and gate 10 to AND(25,32), leaving 53 binary gates. The suffix needs at least nine ANDs that do not read wire 32 and eighteen ORs. Initial constraints used positives 0–51 and negatives 0, 1, 2 and 234; 17,437 variables and 544,051 clauses. The pinned CaDiCaL run with a 90-second CEGIS budget returned **UNKNOWN**, with 56 encoded rows and zero decoded candidates. No unrestricted verdict follows.

Replay with `python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --seconds 90 --solver PATH_TO_PINNED_CADICAL`.

The first unresolved reuse count below the exclusion is h = 28. We ran the same ten-gate prefix a second time with `--min-guard-reads 28 --seconds 120`. Gate nine and ten already consume two reads, so the 53 free gates must consist of 26 more guarded ANDs, nine other ANDs and eighteen ORs. The CNF had 18,868 variables and 546,861 clauses. The result was **UNKNOWN**, still 56 encoded rows and zero decoded candidates. In this option the decoder selects wire 32 if multiple equivalent selectors including 32 are active, preserving the requested count.

For the next session, reuse the stored families for the other 45 viable omissions, or vary the negative-pair witness rule for omissions 26 and 28. The existing rule provably falls short of 257 for those two omissions.

## Pinned project checker

| Standalone theorem | Verdict | Kernel constants | One-file comparison against the checked upstream revision |
| --- | --- | ---: | --- |
| PlaneCase35RescuedGuardSuffix | ACCEPTED (check) | 2,049 | [fork comparison](https://github.com/seankim96/pequalnp-proofs/compare/ec5c3b478f6e7f802dae6582b0feae5cf1a378c1...d884dc812d1232e524802feb582f8f9949968f39) |
| PlaneCase35RescuedGuardSize | ACCEPTED (check) | 2,213 | [fork comparison](https://github.com/seankim96/pequalnp-proofs/compare/ec5c3b478f6e7f802dae6582b0feae5cf1a378c1...8042fde7585cd832a601b8d3519761058560633d) |

Both manifests recorded only their respective research file and the common definitions. All 87 definition digests matched upstream, both expanded theorem statements compiled independently, and the reported axioms were propext, Quot.sound and Classical.choice.
