# L-meta-2625 · Twenty-eight forbidden OR outputs in the 20-read branch

Resumed from `408d4f34774f3f2e8386caadcbaa7f680664e03c`. The checked upstream base is `291ba037b65ad85fcabe7ba3d34710f22dc67e1c`. The fork branch and the author's four closed PRs were checked before starting. #7762 and #8170 were merged with ACCEPTED checker comments, zero review comments and no outstanding review. The upstream tree has reductions 50, 317 and 487 for L-meta-2625. The desk returned not_open for the unit and no gap or lease for the scoped next request. The unrestricted 63-gate question remains open in the checked work. These are fork research contributions.

## Branch and verdict

Start with 26 raw wires and fix case 35 to the following 17 gates, using zero-based wire numbers.

```
OR(0,1)   OR(3,9)    AND(15,27) AND(17,26) AND(13,26) AND(13,27)
OR(2,6)   AND(1,24)  AND(15,32) AND(25,32) AND(0,17)  AND(0,23)
AND(0,25) OR(17,19)  OR(20,24)  OR(39,40)  AND(7,41)
```

Let h count physical AND gates that read wire 32, counting a gate once. Two reads occur in the prefix. Respect the previous checkpoint's 520-row target and its lower bounds. At h ≥ 20 a 63-gate solution must have h = 20. The remaining 46 gates must consist of 18 guard ANDs, nine other (paid) ANDs and 19 ORs. The first paid AND must now follow at least **two** new ORs. At any position in this suffix, an OR computing any of the 28 starting-pair columns in case35-point-seven-shared-first-pairs.json is impossible. The finite case split leaves **202** prospective first-OR values, all of them unions of starting wires. Wire 0 cannot supply either input of the first OR. This is a conditional exclusion within the fixed prefix.

## Two kernel-checked lemmas

| One-file contribution | Checked content | Rechecked constants |
| --- | --- | ---: |
| PlanePointSevenOrOutput · cdfd28e2f404ab2ecb986985ff0d445f03f146c8 | After the first 16 gates, select an arbitrary later OR. If its output is false at pivot 11 and, for each of two 19-flag packings, covers at most one flag whenever false at its negative, the whole suffix requires at least 20 ORs. The selected OR may occur anywhere. | 1914 |
| PlaneMoveDominatingOr · dc12de76724f5bf92e626e09deae6ed03ce4e67c | Replace any selected OR by an OR of two starting wires placed at the front. If its column dominates the selected one on the 52 positives and 468 negatives, the explicitly relabeled circuit remains legal, preserves the total gate count and every starting guard's AND-read count, and dominates the old output at the relabeled index. | 1770 |

The pinned Lean 4.36.0 checker returned ACCEPTED for both, with propext, Classical.choice and Quot.sound. The 87 definition module digests matched upstream in each run. Independent imports compiled the exact saved statements. The first theorem prepends the selected value and replaces the original gate by an AND copy at its slot, keeping all later references. The second theorem constructs an actual circuit rotation in the fixed-size model. The larger case split below uses replayed finite certificates.

## First OR and first paid AND

Before the first new OR, every wire is one of 43 starting signals or that signal ANDed with the guard. The previous checkpoint excludes any paid gate before that OR. The starting signals and guard copies give 73 distinct columns, 2,701 unordered pairs with repetition, and 2,449 distinct OR results. For each excluded result V, preload V as an extra input, delete the selected OR, and use an AND-closed pivot obstruction. Each width-m witness specifies one negative and m positive flags. Every starting wire false there, including V, must cover at most one flag. For a proposed pivot, the program builds **all** conjunctions of pivot-true starting wires and checks that none is live on every listed witness. A live wire is false on the negative and true on at least one flag. This forces at least m new ORs with V already available. Guard copies can be reconstructed with arbitrary ANDs.

A width-19 replay excludes 2,219 distinct outputs. The simple two-packing and pivot condition from the first checked theorem applies directly to 1,928 of the 2,449 values in a numerical evaluation. The 230 surviving values have precisely 230 representations among the 2,701 pairs of distinct semantic operands with repetition. All are ORs of two of the 43 starting columns.

Fix one surviving first union X. Until a second OR or a paid AND occurs, a signal strips to X or a starting column, with an optional guard mask. The previous checkpoint covers all starting-starting paid pairs. X AND X is a copy. For X AND each of the 43 starting signals the new census has 9,890 labeled attempts. Monotone replacement by a previously certified input, a paid preload, X, or their guard copies handles 9,622. Another 267 are excluded by preloading the paid result and requiring at least 20 ORs with the eight paid gates left. The last one, X = OR(14,18) and the other operand wire 1, is excluded by preloading both X and its paid result. Eight paid gates then require at least 19 ORs while only 18 remain. There were 238 distinct supplemental paid-output columns. Masked variants can use one additional free guard AND during reconstruction. None of these counting contradictions assumes a limit on guard ANDs during the preload calculation.

The sharper eight-probe calculation uses the physical fact that a paid output cannot be probed in two distinct receivers. Orient the probes to that same wire in both gates. This would distinguish at most 128 negatives in any eight-bit trace. Each of the cliques used here has strictly more than 128 members. Thus a child-to-parent dependency graph for an orientation has indegree and outdegree at most one. A length-two path admits at most 128 words, and three disjoint implications at most 108. The feasible shapes have zero, one or two disjoint edges up to coordinate permutation. Count the k lightest root-coordinate weights among the allowed words for each shape. Apply the prior exceptional-port clique, compatibility and flag-packing checks. For the last double preload the replay uses 132 negatives and total width 2,182. The unconditional root-weight floor per orientation increases from 260 to 388. This yields the needed 19-OR bound.

## Completing the two first-OR cases

| First OR X | Distinct second-OR outputs | Second-OR outputs still possible | Third-OR outputs after OR(7,13) | Third-OR outputs after OR(13,42) |
| --- | ---: | --- | ---: | ---: |
| OR(0,2) | 2,574 | OR(7,13), OR(13,42) | all 2,708 excluded | all 2,641 excluded |
| OR(0,3) | 2,569 | OR(7,13), OR(13,42) | all 2,703 excluded | all 2,636 excluded |

Preload X and each proposed second union Y. A width-18 pivot certificate contradicts the 17 ORs left after deleting both. For each of the two remaining Y values a paid gate still cannot occur before the third OR. An initial-initial pair was already excluded. For a pair using X and an initial signal, or Y and an initial signal, apply the single-union paid preload analysis to the relevant union. Its argument only uses the total 19-OR budget and availability of that union, so it works with the other OR present. For the cross pair X AND Y, the already excluded X AND wire 13 dominates it on the tested rows. A masked cross pair is recovered with a free guard AND.

Before the third OR every source is therefore an initial input, X, Y, or a guard-masked copy of one of those. Preloading the third union leaves only 16 ORs. For every distinct possible result a width-17 pivot certificate requires at least 17. This completes both fixed first-OR branches. The rotation theorem extends the exclusion to a later OR output with the same tested values, or one dominated by the forbidden column. The output index may be any wire in the lower-bound argument.

## Sharing the pivot witnesses across first unions

For OR(0,4), 2,573 of 2,575 second-OR values are excluded by the width-18 certificates. The same two second choices survive. Their 2,709 and 2,642 third-OR values, respectively, are all excluded. As above X AND wire 13 dominates the cross product. The candidate-witness generator is included so later runs can sample additional packings at any chosen sequence of unions. It replays the selected certificates independently.

The shared-bank replay takes the width-18 and width-17 witnesses used for OR(0,2), OR(0,3) and OR(0,4), applies them to other starting pools, checks every reused packing against the augmented starting wires, and derives fresh pivot certificates. This certifies 22 first values with simple dominance. Five more require a density check after preloading a cross product X AND Y. The ten additional preload certificates (two per first union) each exhibit a clique of 160 and require at least 22 ORs with eight paid gates, exceeding the 19 available. One more first union closes by simple dominance when the full shared bank and original replacement set are used. The 28 verified pairs are stored explicitly. The rotation lemma makes their exclusion valid even at a later OR. After subtracting them from the 230 first-OR candidates, 202 remain.

For the next lexicographic value, OR(2,3), five second-OR columns survive the preliminary width-18 and known-column filters out of 2,577 possible columns. They are OR(7,13), OR(7,15), OR(13,15), OR(13,42) and OR(15,42). In four branches an earlier paid AND is excluded by cross-product dominance and no third OR passes the width-17 replay. Only OR(13,15) remains as a second value. Its cross product and the 17 still-unexcluded third-OR values are the next frontier. Surviving these filters does not establish satisfiability.

## Reproduction

From the fork, use Python with NumPy for the finite replay. All stored witnesses are checked on the original 52 positive and 468 negative rows. Optimization was used to propose witnesses. Replay requires no optimizer, floating-point verdict or trusted search optimum.

```sh
python research/order3_case35_point_seven_or_order.py
python research/order3_case35_point_seven_shared_unions.py
```

To search a new frontier and check the resulting witnesses, the following example prepays OR(2,3) and OR(13,15). Each MILP proposal has a three-second budget. The objective only selects potential flag sets, and the replay checks the actual masks and all residual AND-only candidates. Increasing the samples may find additional witnesses.

```sh
python research/order3_case35_or_packing_search.py --union 2 3 --union 13 15 --samples 90 --seed 2304 --out /tmp/point-seven-2-3-13-15.json
```

For either theorem name N in the table, use the checked upstream base and its pinned toolchain, with the single source and its exact statement copied from the fork.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/$N.lean research/statements/$N.txt check
```

For CaDiCaL, use the same fixed-prefix flags as in the previous checkpoint, with h = 20. A complete common prefix follows. Append the relevant cut, extra gates, and budget.

```sh
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads 20 --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget --preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41
```

Use `--after-fifteen OP A B` for each additional physical gate, then `--seconds B --solver /path/to/lean-4.36.0-linux/bin/cadical`. Budgets are solver seconds, excluding encoding and certificate checks. Runs started with 52 positives and four negatives. A candidate must pass all 520 rows. A solver UNSAT with a replayed cut depends on that cut. Every timeout below returned zero decoded candidates.

| Extra gates | Cut | Budget | Observed verdict |
| --- | --- | ---: | --- |
| OR(0,3) | previous --star-preloads | 60 | UNKNOWN |
| OR(0,3) | new --point-seven-order | 120 | UNSAT |
| OR(0,2) | intermediate cut before its third-OR census | 120 | UNKNOWN |
| OR(0,2) | completed --point-seven-order | 120 | UNSAT |
| OR(0,2), AND(25,43) | one-OR paid cut | 10 | UNSAT |
| AND(13,32), OR(0,43) | first-OR value cut | 10 | UNSAT |
| OR(0,2), separately OR(0,3) | completed --point-seven-order | 10 each | UNSAT in each run |
| OR(0,4), OR(0,3) | completed --point-seven-order, moved late OR | 10 | UNSAT |
| OR(0,4) | --point-seven-order before shared bank | 90 | UNKNOWN |
| free | --point-seven-order | 120 | UNKNOWN |
| OR(0,4), separately OR(11,24) | --shared-first-ors, 22 certified pairs | 10 each | UNSAT in each run |
| free | --shared-first-ors, 22 certified pairs | 120 | UNKNOWN |
| OR(0,7), separately OR(18,24) | --shared-first-ors, 28 certified pairs | 10 each | UNSAT in each run |
| OR(2,3), OR(13,15) | --star-probes | 45 | UNKNOWN |
| free | --shared-first-ors, 28 certified pairs | 120 | UNKNOWN |

## Continuation

Resume at h = 20 with `--shared-first-ors`. For the first candidate OR(2,3), fix OR(13,15) as the second union. Decide whether their cross product can feed the first paid AND before a third OR, and examine the 17 remaining third-OR values if it cannot. The 45-second run on this pair and the 120-second run on the full 20-read prefix both ended UNKNOWN.
