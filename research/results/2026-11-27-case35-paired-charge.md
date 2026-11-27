# L-meta-2625 · Common OR charge and the five-choice cases

Starting checkpoint `f9933c58753d4eaae26e31037f5308a9135c1912`. Checked upstream `a780a67ac0a031a75473f1afb9e7e8a05f102272` still contains the three reductions 50, 317 and 487. The desk said not_open for the unit and returned no gap or lease to the scoped next request. No lease was acquired. The fork refs and author's PRs were inspected. #7762 and #8170 are merged with ACCEPTED checker comments and no outstanding change request. This work is on the research fork.

## Case and budget

Use the same 520 target rows (52 positive, 468 negative) and the following 17-gate prefix with 26 raw wires and zero-based operand indices.

```
OR(0,1) OR(3,9) AND(15,27) AND(17,26) AND(13,26) AND(13,27)
OR(2,6) AND(1,24) AND(15,32) AND(25,32) AND(0,17) AND(0,23)
AND(0,25) OR(17,19) OR(20,24) OR(39,40) AND(7,41)
```

With 63 gates and at least 20 physical ANDs reading wire 32, the checkpoint gives exactly 20 such reads. The suffix has 19 ORs, nine paid ANDs and 18 guard ANDs. Its first paid AND must follow two ORs. The previous checkpoint left 195 potential first-OR outputs. This run excludes 26 more, covering 130 choices of first and second OR together. Each selected first OR had five surviving second values in the previous checkpoint. The replay leaves **169** prospective first ORs in this branch. The unrestricted 63-gate problem remains open in the checked work.

For the previously unresolved X = OR(3,6), Y = OR(13,16), supply X AND Y at the start and delete the paid AND that produced it. The calculation with the eight remaining paid gates uses a clique of 149 negative rows, total packing width 2,546 and a guard-off clique of 112 negatives. The OR floor is 21, exceeding the budget of 19. If the third OR precedes that paid gate, the 12 remaining third values were all eliminated by separately checked width-17 pivot certificates. On these 520 rows representatives of those values are (21,42), (7,21), (18,42), (7,18), (23,42), (7,23), (18,23), (21,23), (25,42), (7,25), (21,25), (18,25).

Across the 26 first ORs, 27 paid crosses used prepaid-intersection certificates, each deleting only the paid gate and preserving the original OR budget. The other crosses had a dominating previously excluded product. The third-OR search contributed 211 distinct (negative row, flag packing) pairs. The stored ledger gives the first operands, second-value counts, paid cross operands, packed rows and guard-off cliques. The verifier rebuilds the finite OR domains and checks every witness before enabling a SAT cut. Each first-OR exclusion uses only the previous checkpoint's excluded columns. No newly excluded first OR depends on another new exclusion.

The targeted algorithm capped individual packing MILPs at one second, and used only feasible flag lists that replay on the actual columns. The cross search capped each of its two clique MILPs at eight seconds and verified the chosen cliques, port restrictions and OR floors. The per-row positive-packing MILPs for the cross had no explicit time limit. The first sweep allowed at most 18 unclosed third values per second OR. A follow-up allowed up to 40 on five first pairs. No failed witness search was counted as infeasibility.

## Kernel-checked sublemma

`PlanePointSevenPairedCharge` uses the 43 prefix wires plus the unmasked (3,6) by (13,16) cross as a free starting wire. Choose any two of the six indexed negative rows 46, 48, 198, 200, 377, 379. If the output rejects both and accepts their designated 19-flag packings, then the number of suffix ORs plus the number of suffix ORs false on **both** selected negatives is at least 36. In a 19-OR suffix this forces at least **17 common false ORs**. The proof combines the two row charges with a gate-by-gate overlap inequality. This theorem alone does not certify the 21-OR floor or the elimination of 26 first ORs.

Lean 4.36.0 project checker: ACCEPTED (check), 2,071 constants kernel rechecked, axioms propext, Quot.sound and Classical.choice. An independent import compiled the exact statement. All 87 definition-module digests matched upstream. One-file fork branch `research/l-meta-2625-case35-paired-charge`, commit `7a9789fd90fb057003825e5763ec354904cb93e8`. There was no open assignment for an upstream PR.

## Replay and continuation

Run `python research/order3_case35_point_seven_paired.py` to replay the new census, or use `--shared-first-ors` with the physical prefix and other switches in the previous checkpoint's command. For a fixed pair, append `--after-fifteen OR A B`. The pinned CaDiCaL starts with 52 positives and four negatives. The SAT budget starts after constructing the initial encoding and replaying the cuts.

Next candidate X = OR(2,5). Eight second-OR values survive. All eight crosses have dominating replacements. With the enlarged bank and cumulative exclusions, the remaining third counts are 1 for (15,42), 1 for (7,15), 0 for (13,42), 0 for (7,13), 2 for (13,15), 1 for (25,42), 1 for (7,25), and 2 for (13,25). Target the two values after (13,15) first. These are candidate counts, not evidence that a circuit exists.

For the (2,5) then (13,15) continuation, the two remaining third unions have raw operand pairs (7,25) and (25,42).

| Suffix after the 17 gates | Cut | SAT-loop budget | Observed verdict |
| --- | --- | ---: | --- |
| OR(3,6), OR(3,11), OR(24,25), tested separately as the first suffix gate | cumulative 61 excluded first ORs | 10 s each | UNSAT on the initial 56 encoded rows in each run |
| OR(2,5) then OR(13,15) | previous star probes | 45 s | UNKNOWN, 56 encoded rows, zero decoded candidates |
| Free suffix, h ≥ 20 | cumulative 61 excluded first ORs | 60 s and 90 s | both UNKNOWN, 56 encoded rows, zero decoded candidates |
