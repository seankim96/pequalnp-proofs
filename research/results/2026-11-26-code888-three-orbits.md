# L-meta-2625, case 6, code 888: three residual orbits

Parent `21a1b06c36112b091b24edb0ad12624ea24b5357`. The physical prefix is AND(0,13), OR(0,14), AND(1,13), AND(1,18). On the 52 positives and 468 negatives, the prior pinned Lean checker accepted a nine-AND suffix bound and the conditional first-AND reduction. The unconditional 63-gate question remains open.

## Finite first-AND calculation

Run `node research/order3_code888_first_and_orbits.mjs`. The emitted JSON includes zero-based indices for the common 257-negative certificate. The calculation enumerates all relevant operand pairs and directly verifies the transported certificate for all 40 exceptional pairs. It completed without a timeout. It makes no SAT call and puts no bound on how many OR gates precede the first further AND.

Before that AND, every operand is an OR of starting wires. Wire 27 is already an OR of raw inputs. The other three derived wires 26, 28 and 29 are zero on every negative and contribute a total of three distinct positive flags. If A and B are the raw supports of the two disjunctions, the new column equals OR(A) AND OR(B) on negatives. Its positive support is contained in that column's positive support union the three flags. This gives one pessimistic column per unordered pair of raw supports. Constant false is the empty disjunction. An operand containing constant true is uniform.

Two negatives conflict if their union on the 30 starting wires covers no positive. There are 54 disjoint conflict edges. For any selected-set bit mask S, its largest independent subset has size |S| minus the number of edges entirely in S. This gives a 414-negative base family. To preserve a witness after adding the AND, it suffices to drop all negatives with operand values (1,0), or all with values (0,1). In the first orientation each retained negative with left operand true has right operand true; the symmetric argument applies in the second. Every OR of starting wires preserves a positive witness covered by the union. Consequently these checks allow arbitrary previous OR gates.

If either operand is constant on 257 independent negatives, it works against every other operand. Each singleton has at least 294 independent negatives on which it is false. Each four-element raw support has at least 271 independent negatives on which it is true. Monotonicity covers all larger supports. The only balanced supports are 325 pairs and 940 triples, 1,265 total. Identical operands preserve the base witnesses.

The 24 enumerated permutations preserve both labeled row sets, the three ideal flags as a set, and the raw OR closure. They act on the path 0--13--1--18 in either direction. The code verifies bijectivity, row-set preservation and group closure. It uses these symmetries only on the normalized first-AND problem; the physical OR(0,14) need not be fixed. A direct scalar replay on all residual images checks this use of symmetry.

The 1,265 balanced supports give 799,480 unordered distinct pairs and 35,541 orbits. The matching criterion closes 35,538 orbits. The three remaining representative pairs are:

| Raw support A | Raw support B | Orbit size |
| --- | --- | ---: |
| {2,4,10} | {1,14} | 4 |
| {14,17} | {4,16} | 24 |
| {15,17} | {4,5} | 12 |

The union of all three representatives' pessimistic positive supports is mask `0x1604e3`, flags 0, 1, 5, 6, 7, 10, 17, 18 and 20. Omitting these nine flags leaves 43 positive witnesses. Greedy selection finds 310 negatives for which every pair covers at least one of the 43. The first 257 sorted indices suffice. The verifier checks 32,896 pairs for this common family, then checks every one of 1,315,840 negative pairs on the lifted 31-wire rows of the 40 residual syntaxes. It performs the latter tests using scalar wire values rather than reusing the conflict-graph witness bits.

The earlier Python study and this independent JavaScript verifier both support at least ten AND gates after gate four in code 888, including the first subsequent AND. The concrete finite premise still needs a Lean checker verdict. The SAT driver continues to use nine AND and eighteen OR. For a 63-gate candidate there are 59 free slots after gate four; even the proposed strengthening accounts for only 28.

## Lean handoff and exact verdict

`research/candidates/Plane888NineFlags.lean` and `research/statements/Plane888NineFlags.txt` are a prepared source and expanded statement for the common certificate. To check, copy the candidate into `lean/PEqualNP/Research/Plane888NineFlags.lean` in the research checkout and run the repository checker on that path and the statement in check mode, with pinned Lean 4.36.0. Its claim is conditional: if the first AND after an arbitrary OR prefix is positive only within the nine flagged rows, at least nine AND gates are still needed strictly after it. Negative values of that gate are unrestricted. The candidate validates the positive witness for each selected pair against the actual positive and negative row words. An independent arithmetic replay checked all 32,896 witness indices used in the candidate.

No new Lean theorem was accepted in this run. An initial full-graph build exposed a decidability elaboration error. The corrected build lost its execution environment before a verdict could be recovered. The smaller common-certificate candidate is uncompiled. Next check that candidate, then connect the matching criterion and the finite orbit cover to the accepted first-AND reduction. No new 63-gate SAT search was run.

The desk reported another holder of L-meta-2625. This session did not take, renew or release a standard lease. Existing PRs #7762 and #8170 were merged with accepted checker reports and no review requests. No upstream PR was submitted.
