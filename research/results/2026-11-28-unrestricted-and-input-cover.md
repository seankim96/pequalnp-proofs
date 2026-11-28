# L-meta-2625 · Covering the input pairs of binary AND gates

Research parent 97b63670c019bf5ff0c6ccadffa61c4581cda01b. Checked upstream base 5245ce9b3b1f1262390339d02ec9b87801b579bf. The unrestricted size-63 question remains open.

## Necessary condition for every circuit passing the desk tests

For each AND gate with two distinct operand indices, draw an undirected edge between those two wire indices. A cover is a list of indices meeting every edge. PlaneAndInputCover proves that every cover has at least nine entries. If it has exactly nine, every entry must be an internal wire (index at least 26). The theorem uses the project's Circuit, Monotone2 and circuitFun definitions, all positive incidence flags, and the eight negative representatives under the prescribed multipliers, translations and duality. It permits arbitrary sharing, any output, both constants and unary gates, and the project's default value for missing wires. It fixes no prefix and imposes no size bound.

The proof gives a further conclusion for every such cover. There exist 468 desk-negative inputs whose vectors of values on the covering wires are all distinct. A nine-wire cover therefore uses 468 of its 512 binary patterns. Fixing one coordinate permits at most 256 negative rows of either value. On the 468 certified rows every primary input is zero 342 times. Choosing a primary input for a nine-wire cover would exceed 256. In particular, every passing circuit has at least nine distinct-input binary AND gates, because one operand per such gate always gives a cover. The target lower bound on total gate count remains unresolved.

For a circuit with exactly nine distinct-input binary AND gates, either operand of any one gate can be included in a cover by choosing one input of each other gate. Therefore both operands of the first such AND must separately be true on 212–256 negatives. Before that gate, every signal is a constant or an OR of raw inputs: unary and repeated-input ANDs copy their operand, and a nullary AND gives true. Direct enumeration gives 126 true negatives for a singleton, 204, 225 or 252 for a two-input union, and at least 270 for every three-input union. Larger supports also have at least 270. Thus each operand of the first distinct-input AND must be an OR of precisely two distinct primary inputs drawn from the 156 pairs of weight 225 or the 52 pairs of weight 252. The other 117 pairs fail the marginal constraint. This additional restriction combines the kernel-checked injectivity theorem with the reproducible finite support enumeration. These 208 pair columns are distinct. Across their 21,528 unordered pairs of different supports, the first AND output is true on 48–174 negatives. Such an output lies outside the required 212–256 interval, so no later distinct-input AND can read it directly in a circuit with only nine such gates. If the first AND reads two copies of the same support, a unary copy can replace that AND on all tests, contradicting the nine-gate lower bound. The marginal constraint leaves 208 possible OR supports for one operand. It does not supply a circuit.

For two negative rows with identical cover observations, consider a positive row contained in their bitwise union. Gate induction shows that every wire true on the positive must be true on at least one of the two negatives. At a binary AND the covered operand has the same Boolean value on both negative rows, which is exactly what the induction step needs. Previously computed wire values persist, and a premature read yields false on both rows. A separating positive exists for distinct negative masks because for every absent primary bit the proof checks an incidence flag contained in the mask after that bit is added. The contradiction at the circuit output proves injectivity. The certificate supplies actual orbit keys for every negative row, checks their desk membership and evaluation in Lean, and checks that the 468 masks are strictly increasing.

The project-pinned Lean 4.36.0 checker returned **ACCEPTED (check)** on the exact research statement. It rechecked 2,831 constants, with propext, Classical.choice and Quot.sound. All 87 project definition digests in the checker manifest matched the upstream sources. The published proof bytes matched the manifest. An independent import elaborated the exact statement. An earlier certificate layout ended with verifier exit 137 and no verdict. A subsequent draft had a cardinality simplification error. The final file checks each negative certificate as a separate declaration and uses an explicit cardinality calculation.

## Applying the verified condition to fixed prefixes

Let K be a minimal cover of the AND edges already present in a prefix. If the largest group of negatives with identical values on K has M rows, a full cover containing K needs at least |K| + ceil(log2 M) entries. This follows from injectivity on the full cover. Each full cover contains at least one minimal prefix cover, so the minimum of this lower bound across those choices applies to every completion. The Python enumeration works on the 468 negative rows. It was cross-checked by directly enumerating all subsets of prefix edge endpoints for all 68 two-gate representatives and by separately evaluating wires on each negative for the 17-gate prefix.

Two-gate cases 0–18 inclusive and case 60 require at least ten covering wires. The other 48 have a lower bound of nine by this calculation. For case 35 the floors after 7, 8, 9, 10, 13 and 17 fixed gates are 9, 10, 10, 10, 11 and 12 respectively. Of the 44 minimal covers of the 17-gate prefix, 12 require at least 12 entries after extension, 30 require at least 13, and 2 require at least 14. These figures are an application of the theorem by finite enumeration. They are not additive gate charges.

## Case 35 search with the 17-gate prefix and h=20

The suffix budget has 19 ORs, 18 guard-reading ANDs and nine other ANDs. All integer packing certificates use 52 positives and 468 negatives. The previous checkpoint had 173 of the 230 possible first OR values excluded. The cumulative verifier now excludes **191 of 230**, leaving 39 unexcluded. Unexcluded columns describe the search frontier and need not occur in any completing circuit.

| First OR | Second columns | Third-OR orders | Fourth columns | Explicit paid products after three ORs | Two-OR cross certificates | Search seed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| (11,22) | 19 | 10 | 28225 | 16 | 2 | 3701 |
| (22,25) | 24 | 10 | 28237 | 16 | 1 | 3702 |
| (4,18) | 23 | 20 | 56498 | 18 | 2 | 3703 |
| (10,18) | 25 | 12 | 33916 | 12 | 2 | 3704 |
| (15,25) | 24 | 26 | 73460 | 34 | 0 | 3705 |
| (18,22) | 27 | 24 | 67768 | 30 | 1 | 3706 |
| (5,23) | 23 | 4 | 11270 | 10 | 1 | 3707 |
| (22,23) | 26 | 4 | 11306 | 0 | 0 | 3708 |
| (5,12) | 26 | 0 | 0 | 0 | 1 | 3709 |
| (16,18) | 23 | 4 | 11300 | 0 | 0 | 3710 |
| (21,25) | 23 | 10 | 28257 | 16 | 0 | 3711 |
| (11,18) | 23 | 18 | 50837 | 16 | 1 | 3712 |
| (5,25) | 26 | 16 | 45182 | 26 | 0 | 3713 |
| (16,23) | 24 | 8 | 22604 | 10 | 0 | 3714 |
| (5,14) | 27 | 28 | 79110 | 26 | 0 | 3715 |
| (5,21) | 27 | 6 | 16945 | 6 | 0 | 3716 |
| (18,25) | 27 | 14 | 39535 | 16 | 0 | 3717 |
| (7,8) | 23 | 0 | 0 | 0 | 6 | 3718 |

The 18 ledgers cover 440 second-column cases, 214 ordered triples, and 604,450 fourth-column candidates counted per order. They include 252 exceptional paid products and 17 exceptional two-OR crosses. In the ledger for X=(11,22), the (15,42)/(5,13) order reused the previous seed-3613 certificate for 2,790 fourth columns. The remaining 213 records were generated here. The formerly UNKNOWN order (11,22)/(7,15)/(5,13) excludes all 2,860 fourth columns, with all its possible paid products dominated. Each of the two exceptional crosses for first (11,22), with second (5,21) or (5,23), forces at least 22 ORs against the available 19. After the ten third-OR orders and these crosses were checked, the whole first (11,22) branch was excluded.

Width-16 packing discovery used one initial objective and up to 40 randomized objectives per negative, with three seconds per MILP. Clique MILPs used up to eight seconds. Auxiliary 52-variable packing MILPs for paid products had no explicit per-call time limit. Each group of third-OR worker processes had a 240-second outer limit. Integer replay checks the saved witnesses without invoking MILP. Fixed cut-assisted CaDiCaL queries for first (11,22) and triple (11,22)/(7,15)/(5,13) each returned UNSAT at a ten-second solver budget on 56 encoded rows. The free suffix at sixty seconds returned UNKNOWN with zero decoded candidates.

The next open order is (8,13)/(21,42)/(13,18). Direct CaDiCaL at 45 seconds returned UNKNOWN on 56 encoded rows with zero decoded candidates. The unrestricted 63-gate question is open.

## Reproduction

Run from the research checkout with the pinned Lean distribution and packages.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/PlaneAndInputCover.lean research/statements/PlaneAndInputCover.txt check
python research/order3_and_wire_cover.py
python research/order3_case35_or_frontier.py 8 13
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads 20  --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget  --preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41 --star-probes --after-fifteen OR 8 13 --after-fifteen OR 21 42 --after-fifteen OR 13 18 --seconds 45 --solver "$(lean --print-prefix)/bin/cadical"
```

The desk marked this assignment not open for allocation and issued no lease to this run. The inspected upstream tree has three reductions and no direct solution of the unrestricted target. The four account PRs are closed. Both #7762 and #8170 were merged following accepted checks, and their review timelines contained no actionable change requests. A final upstream check at 1d99eb8c28c1ae078487c4b17bcaa0192bce1863 still found the same three reductions. The checker, pinned configuration and all checked definition files were unchanged. The 18 ledgers first landed in numerical checkpoint 075728ef7efc0c1fa6f0f231319563e5472392e2. The one-file proof commit on the fork is 2318b8964bc8aa14aeec89c7207fcc830c603086.
