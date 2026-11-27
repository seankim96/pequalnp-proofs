# L-meta-2625 · Silent OR gates and a fourth-OR census

Resume from `e7a02ef9a4aadea75cd065b6c22e9df197e36ac4`. Upstream at `ea6d69e990cb6220e65c0823031c40126c3b60b1` still contains reductions 50, 317 and 487. The desk returned not_open for L-meta-2625 and no gap or lease on the scoped next call. The author's four PRs and fork branches were inspected. #7762 and #8170 are merged with ACCEPTED checker comments and no requested changes. This is work on the fork.

## Scope and verdict

Use the previous report's case-35 prefix of 17 physical gates, the 26 original inputs, 52 positive rows and 468 negative rows. Wires and row indices are zero-based. The 63-gate branch with at least 20 ANDs reading physical wire 32 requires exactly 20 such reads. Its suffix has 19 ORs, nine other ANDs (paid ANDs), and 18 guard ANDs. All counts below concern this branch. No unrestricted 63-gate lower bound follows.

The previous checkpoint left 169 first-OR values. The extended third-OR census excludes 55 more, checking all 630 first/second continuations for those 55 candidates. Eighty-eight paid crosses used unmasked paid-result preloads; the other crosses used a previously checked dominating replacement. The second/third replay added 181 distinct negative-row/flag packings to the previous 211. The 392 supplemental packings are joined with the older bank at verification. Each stored case is verified against the earlier fixed exclusions without dependence on any other first pair in the same compressed ledger.

For X = OR(2,5), all eight second unions were covered. The eight remaining (second,third) choices in the previous checkpoint, including ((13,15),(7,25)) and ((13,15),(25,42)), each yielded a targeted width-17 pivot certificate. For this first pair, all paid crosses have dominating replacements. This closes both alternatives for when the first paid AND occurs.

For an additional first OR, X = OR(4,19), there were eleven second choices; all eleven crossed paid products have a dominating replacement. After applying the enlarged bank, only four third cases remained. In these four cases Y is OR(7,13) or OR(13,42), and Z is Y OR wire 23 or Y OR wire 25. Wire 44 denotes Y when the two ORs are placed directly after the fixed prefix.

* Before a fourth OR, a paid gate's operands are among the starting wires and X,Y,Z up to guard masking. Products not using Z already have exclusions. Of all Z-products, only Z AND wire 0 and Z AND wire 26 were left by the copy and dominance checks, in each triple. Prepaying each of those products separately, while still charging all three ORs, gives an OR floor of **22** with eight paid ANDs left, against a budget of 19. Eight prepaid-result certificates are checked.
* If a fourth OR occurs before the first paid AND, prepay X,Y,Z and charge their three ORs. The width-16 pivot test excluded all 2,842 possible fourth outputs for each triple with Y = OR(7,13) and all 2,777 for each triple with Y = OR(13,42). The counts are distinct within a triple; they need not be distinct across triples.

Thus OR(4,19) is also excluded as a first OR. Including all previous exclusions, **113 of the original 230 prospective first-OR outputs remain**, down by 56 this session. The OR relocation result from the earlier checkpoint licenses use of these starting-pair exclusions later in the suffix as well.

## Lean contribution

`PlanePointFiveSilentOr` fixes the 17 gates and OR(2,5). For each of three negative inputs (negative row indices 48,198,200) it lists 19 designated positive inputs. If a suffix rejects that negative, accepts its designated positives and uses at most 18 ORs, **every suffix OR outputs false on that negative**. The proof allows any number of suffix ANDs and any output index. It splits the suffix at an arbitrary OR. A true output at the selected negative would leave at most 17 false ORs there, while its flag packing requires 18. The lemma formalizes this gatewise constraint; the larger first-OR census uses separately replayed finite certificates.

The pinned Lean 4.36.0 project checker returned ACCEPTED (check), with 1,939 constants rechecked and axioms propext, Quot.sound and Classical.choice. An independent Lean import compiled the exact saved statement; all 87 definition-module hashes matched the checked upstream revision. The single new file is on fork branch `research/l-meta-2625-case35-silent-or` at `7e1270de63a2c001323e1b39b39c1cd7f14b0600`. The desk did not issue an assignment for an upstream PR.

## Solver budgets and reproducibility

The targeted searches used a one-second MILP cap per proposed width-17 packing. The first sweep capped remaining third values at 45 per second choice, then retried five hard first pairs with a cap of 120. Failed witness searches supplied no exclusion. Cross preloads used up to eight seconds per clique MILP and uncapped per-row packing MILPs, followed by exact finite replay. The four fourth-OR searches used width 16, seed 2601 and up to 40 randomized proposals beyond the first proposal per negative; each MILP had a three-second cap. No timeout implies infeasibility.

Run the frontier query from the repository root to verify the saved first-pair and fourth-OR certificates and print the residual choices for the named first union.

```sh
python research/order3_case35_or_frontier.py 4 5
```

For SAT, use the previous checkpoint's case-35 command and pinned CaDiCaL binary. Each run began with 52 positive and four negative rows. The SAT-loop budgets exclude setup and finite certificate replay. A cut-assisted UNSAT depends on the replayed cuts.

## Next unresolved case

For X = OR(4,5), seventeen second values remain. All seventeen have a dominating replacement for their first paid cross. Fourteen permit no third OR under the current cuts. For Y = OR(10,13), the two unresolved third values are OR(7,22) and OR(22,42). For each of Y = OR(7,13) and OR(13,42), four third values remain: Y OR input 8, 10, 11 or 12. Test the paid products involving Z and the fourth union for these triples. These are unresolved candidates, not circuit witnesses.

| Gates fixed after the 17-gate prefix | Cut | SAT-loop budget | Verdict |
| --- | --- | ---: | --- |
| OR(2,5), separately OR(24,42) | third-OR ledger, 116 excluded first values | 10 s each | UNSAT on 56 encoded rows in both runs |
| Free suffix | third-OR ledger, 116 excluded first values | 60 s | UNKNOWN, 56 encoded rows, zero decoded candidates |
| OR(4,19), OR(7,13), OR(23,44) | previous star probes | 45 s | UNKNOWN, 56 encoded rows, zero decoded candidates |
| OR(4,5), OR(10,13), OR(7,22) | previous star probes | 45 s | UNKNOWN, 56 encoded rows, zero decoded candidates |
| OR(2,5), separately OR(4,19) | complete ledger, 117 excluded first values | 10 s each | UNSAT on 56 encoded rows in both runs |
| Free suffix | complete ledger, 117 excluded first values | 75 s | UNKNOWN, 56 encoded rows, zero decoded candidates |
