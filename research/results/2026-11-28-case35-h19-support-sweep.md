# L-meta-2625 — Pure positive supports in the case-35 AND–OR–AND frontier

Parent f168d6f4d9063901493e797cc40b00c228609e79. Fix the 17-gate prefix PREFIX13 + POINT7, size 63, and exactly 19 physical guard reads (AND with wire 32). Consider the suffix with 10 ordinary ANDs and 19 ORs. Write A for its first unmasked ordinary product, X for the next OR, and P for a proposed third non-guard operation which is an AND. Possible guard masks between the three are included. The previous checkpoint left 55,915 triples among 30,532 (A,X) pairs. All results below concern this prefix, split and order.

## A fixed first AND

For AND(26,41), the earlier frontier had 564 middle-OR values and 1,003 triples, with 725 distinct third products. The maximal third products under signed dominance number 324. For each, supply A and this product as starting columns, retaining every old input. The middle OR can be evaluated with its original operands or their replacements. The remaining circuit has at most eight ordinary ANDs and nineteen ORs with arbitrarily many free guard masks. Independent replay gave floors of 20 ORs for 4 representatives, 21 for 107 and 22 for 213. For each of the 725 products the independent replay also found a dominating representative. Thus when the first ordinary gate is AND(26,41) and the second non-guard gate is an OR, a third ordinary AND is excluded for every choice of this OR. The previous checkpoint covers middle gates and products outside the 1,003 outstanding triples.

## Transport between starting pools

A 520-bit column c supplies v when c is at least v on all 52 positive rows and at most v on the 468 negative rows. Replacing any collection of wires in this direction preserves separation by monotone gates. In particular a column with zero negative bits supplies every wire whose positive support is contained in its own. For a finite collection of ordinary columns a single signed column can supply them all: take the union of their positive bits and the intersection of their negative bits. There is no requirement that artificial starting columns be realizable by the original circuit. Each is offered to a stronger problem, on which a witness **lower** bound is required.

For each pair of artificial or actual columns c,d, allow c,d and their guard masks to be used without paying ordinary gates. There are two ways to use a verified floor.

* If they supply A and P, the original middle OR is retained (or rebuilt) and all nineteen ORs remain in the relaxed budget. A floor of twenty suffices.
* If they supply A, X **and** P, delete the middle OR as well. The budget is now eighteen ORs. A floor of nineteen suffices. One supplied wire can replace several gates. The OR's operands can be ignored in this test.

In either case two ordinary ANDs have been removed, justifying the eight-probe trace test. Free guard masks absorb the masks appearing on original products. In the second test an artificial column supplying X need only agree in the signed direction. Being equal on positives and false on additional negative rows is safe, even if other gates of the suffix also read X. Discovery included pairs of pure flag sets, a single pure union covering several sets, the maximal actual target pairs, a middle OR and third product sharing one paid-for substitute, and signed joins for groups of products. Only certificates tested on the full augmented starting pool enter the counts.

## Census

The retained ledger consists of 2,972 checked starting pools. Of these, 1,830 have only positive bits in both columns. There are 2,513 standard records and 459 strengthened operand-trace records. The checked floor distribution was 19 on 16 pools, 20 on 1,303, 21 on 1,097 and 22 on 556. Rebuilding the middle OR excluded 39,649 triples. Removing it as well excluded 5,275; the sets overlap on 5,140 triples. The three ledger files have the same record encoding as the parent. The replay checks their SHA-256 digests and enumerates the overlap between its two exclusion tests before counting the surviving triples.

| Quantity | Parent | New checkpoint |
| --- | ---: | ---: |
| Unexcluded (A,X,P) triples | 55,915 | 16,131 |
| Unexcluded (A,X) pairs out of 165,204 | 30,532 | 9,482 |
| Distinct middle OR columns X with any survivor | 585 | 359 |
| Unexcluded triples with A = AND(26,41) | 1,003 | 0 |

Thus 39,784 additional triples and 21,050 additional (A,X) pairs were excluded. The cumulative order restriction holds for 155,722 of 165,204 normalized pairs. Thirteen of the 65 useful first products are completely excluded in this order. For every remaining triple, X is true on at least five of the 52 positives, and P is true on exactly two, three or five positives. The surviving support classes of P contain respectively 9,087, 3,388 and 3,656 triples. The entire table counts normalized truth columns, rather than syntactic circuits.

The targeted small-middle sweep used signed joins of X and P. The large-third-product sweep grouped first products with overlapping support, followed by exact signed first-product representatives. A final sweep for third supports of four and six used 383 representatives across 23 distinct P columns, returning standard floors 21 or 22 for all 383. The original AND(26,41) representatives are retained explicitly for separate replay. The additional exceptional-fiber search was stopped after 580 of its candidate records had been independently validated; the compressed ledger includes the records retained for coverage. No unsolved candidate was assigned a negative solver verdict.

A concrete next slice is A = AND(3,15). Its 173 pending triples span 117 middle OR values and 151 third products. The Python replay returns this ground set, so the next sweep can start directly from those actual values. A second approach is to target all third products covering five positives, currently the largest surviving support size.

## Reproduction

Run `python research/order3_case35_h19_support_sweep.py --recheck-parent` from the fork root. This checks the preceding two-source ledger first, then the new ledger. The default skips rechecking the immutable parent witnesses, verifies their compressed SHA-256, recomputes the parent frontier, and checks every new witness. Each witness contains positive-row packings, a clique of distinguishable negatives and a guard-false clique. Strengthened records add exceptional-port fibers, incompatible pairs and, where needed, constant-port witnesses from the previous checkpoint’s operand-trace test. The verifier rebuilds the incompatibilities and derives its integer OR floor. Packed integers in the gzip ledger index these finite sets. The retained pools cover the results independently of any discovery ordering or optimization objective.

Discovery used HiGHS through SciPy MILP with eight seconds per negative-clique optimization and no separate time limit for each 52-flag packing. A feasible clique or packing only contributes through the replayed bound. The independent pinned CaDiCaL query fixed the same prefix then AND(26,41), OR(14,18), AND(1,44), with at least 19 guard reads and no prescribed ordinary split. With a 90-second solver budget it returned **UNKNOWN**, 56 encoded rows and zero decoded candidates. This broader query certifies no exclusion.

From a checkout using the pinned toolchain, the broader solver query can be repeated with

```sh
solver="$(cd lean && lean --print-prefix)/bin/cadical"
python research/order3_prefix_search.py --case 35 \
  --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 \
  --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 \
  --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 \
  --operator-bounds --shared-guard-budget --min-guard-reads 19 --eleventh AND 0 17 --wire-credit \
  --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget --preloaded-trace \
  --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 \
  --after-fifteen OR 39 40 --after-fifteen AND 7 41 --star-probes \
  --after-fifteen AND 26 41 --after-fifteen OR 14 18 --after-fifteen AND 1 44 \
  --seconds 90 --solver "$solver"
```

## Desk and upstream

The project's public record at https://data.pequalnp.com/data/lemma/L-meta-2625.20e5c8a55a15.json gives the unit status as `conjecture` (public snapshot generated 2026-11-28 06:39:21 UTC). The proposition asks for existence of a separator of size at most 63. No unrestricted circuit was found here and the restricted exclusions do not establish its nonexistence. At upstream cdf085a5c060c21e39b168881866aabc078d5ed2, and again at 07feb24658c8882d9a3f714fdd5ec556aa6be941, there were three reduction files R_meta_2625_50, R_meta_2625_317 and R_meta_2625_487. The targeted desk request returned no lease. There was no lease to renew or release and no upstream submission. PRs 7762 and 8170 are merged with accepted checks and no outstanding review threads.

