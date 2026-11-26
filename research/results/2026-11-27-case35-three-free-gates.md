# L-meta-2625 — case 35, two free gates after a guarded pool, and a reduction for three free gates

This session builds on research commit `1aac033f1f1837a517ed13d3ab37d0b09b727b0b`. The unrestricted 63-gate circuit question still has no verified verdict here. The desk returned `not_open` for L-meta-2625, which does not distinguish a checked assignment from a withdrawn one. The upstream snapshot used for verification is `452fe2617df71cd9f8d417e86c4439f0fe6427e9`. It contains the three reductions R_meta_2625_50, _317 and _487. All four seankim96 PRs were merged. #7762 and #8170 each have an ACCEPTED checker comment and no outstanding review requests or inline comments. The full fork head list was inspected. The desk also returned not_open for all five prepared standard branch IDs (2159, 2276, 2384, 2984, 3469). No lease was acquired, renewed or released; the research files are on the fork.

Indices below are zero-based. The fixed four gates are OR(0,1), OR(3,9), AND(15,27), AND(17,26). The two following gates in the principal example are AND(13,26) and AND(13,27), in either order. Test row order is the canonical 52 positives, then 468 negatives.

## Proved suffix bound

**PlaneCase35GuardedPoolTraceBound** accepts a pool of arbitrary size. Every wire is either exactly a baseline four-gate wire or is false on every positive outside {0,1,2,3,16,40}. Extra wires can have arbitrary values on negatives. Append ANY two binary AND/OR gates, with the second allowed to use the first. Every suffix separating the 520 tests then needs at least nine AND gates.

The new charge certificate discards 120 negative rows permanently. Up to two additional exceptional positives cost at most 44 negatives each. At least 260 negatives remain, above the 256 traces available from eight ANDs. An independent Python replay checked all 60,378 unordered pairs among the 348 negatives outside the permanent set.

For the four previously studied eight-gate prefixes with AND(0,17), AND(0,23) at seven and eight in either order, this covers all 22,657,600 ordered choices of ninth and tenth gates, including dependencies. If both are ANDs, the separate established 19-OR bound after gate four implies **at least 38 total gates**. Broader numerical census: after either fifth/sixth order there are 870 AND and 16 OR seventh choices satisfying the silence condition, and 850,560 guarded seventh/eighth pairs per order. Free choices at nine and ten bring the family to 9,635,824,128,000 ordered encodings. These are syntactic multiplicities. Commuted operands and equivalent functions are counted separately.

A longer excluded family follows from the same theorem. Fix 30 guarded AND gates after the first four and allow two arbitrary further ANDs. A successful completion would need at least 4 + 30 + 2 + 9 + 19 = 64 gates. The replay constructs a prefix with 30 distinct non-baseline signals, all nonzero on some negative. This exclusion requires those prefix conditions.

## Checked reduction for arbitrary gates seven through nine

**PlaneCase35ThreeFreeGateReduction** allows all three binary gates and all their dependencies after the fixed six gates. With at most six fresh operand occurrences there are 288 operator/dependency patterns. Fresh operands may denote the same old wire. The three outputs have disjunctive normal forms which together use at most four distinct products of two or more operands. Each such product either copies a base signal or can lose the pair witness on at most one high positive. This yields one common omission set of size at most four. The formal reduction shows that proving the following finite premise gives a nine-AND suffix after gate nine:

For each set S of up to four positives, exhibit at least 257 negatives such that every pair has a baseline witness among positives 4 through 51 outside S. A baseline witness is a positive whose active baseline wires are all present in the union of the two negatives. The final reduction contains the three-gate structure proof and the pigeonhole argument in the same file. Its quantifiers allow arbitrary suffix length, fan-out and output wire, as well as constant true and false in the suffix pool.

## Remaining finite certificate

For each negative pair i < j, form its set W of high baseline witnesses. For every W with at most four elements, initially put j in bucket W. Remove from each bucket endpoints already appearing at a proper submask. For a given omitted set, the union over its submasks is unchanged. There are 1,932 nonempty buckets and 3,812 endpoint memberships. Of 109,278 negative pairs, 90,764 have at least five high witnesses. The other 18,514 each have a bucket containing the higher endpoint, with mask contained in W. This local condition suffices for the separation premise.

The empty bucket costs 96. For each of the 17,296 triples take twice the sum of its singleton costs, three times the sum of its pair costs, and six times its own cost. The maximum is 162. Summing over the four triples of an omitted quartet counts each lower-order cost six times. Each four-mask has residual cost at most two. The uniform discard cap is therefore 96 + 4 × 162 / 6 + 2 = 206, leaving at least 262 negatives. Direct enumeration checks all 194,580 quartets. The largest sum before the uniform relaxation is 194. Smaller omissions are covered by extension to a quartet. Python independently matches all 213,052 one- through four-flag costs to the packed Lean tables.

**Remaining Lean obligation**: connect the packed bucket costs to actual endpoint membership and baseline witnesses on the 520-row data. A compact proof can encode each bucket as an image of at most its recorded number of endpoints, and verify the five-witness-or-bucket condition for all i < j. The numerical replay establishes these facts computationally. The formal reduction alone does not give the unrestricted three-free-gate suffix bound.

## Solver runs

Both experiments fixed the first eight gates in the listed order. The solver was CaDiCaL from the pinned Lean 4.36.0 distribution, total budget 63 gates, 53 free gates. Both started with all 52 positives and four negative seeds (0, 1, 2, 234); every decoded model is replayed on the full 520 tests.

| Last two gates | Required suffix AND / OR | Initial variables / clauses | Budget | Verdict |
| --- | --- | --- | --- | --- |
| AND(2,16), AND(3,34) | 9 / 19 | 17,013 / 543,202 | 120 s | UNKNOWN; 56 encoded rows, zero decoded candidates |
| OR(2,4), AND(14,34) | 9 / 18 | 16,960 / 543,096 | 180 s | UNKNOWN; 56 encoded rows, zero decoded candidates |

The dependent tenth wire in the second experiment accepts precisely positive indices 5 and 6 and rejects all 468 negatives. That wire is a local signal. A full witness must also accept the remaining 50 positives.

Run `python3 research/order3_case35_guarded_pool.py` and `python3 research/order3_case35_four_omission_cost.py` from the research branch. Replay either SAT row with the chosen last two gates:

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh AND 0 17 --eighth AND 0 23 --ninth OR 2 4 --tenth AND 14 34 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --seconds 180 --solver /path/to/pinned/cadical

The second run complements the 120-second branch by keeping a useful two-flag dependent output. For a different continuation, enumerate further useful multi-flag gate outputs or certify the bucket-to-witness correspondence.

The threshold-dispatch regression check exercised 18 branches, including reversed orders, eligible and ineligible pools, mixed-type prefixes and an unrelated case. The new SAT constraint uses only the proved guarded-pool bound.


## Verification against upstream

The pinned Lean toolchain is leanprover/lean4:v4.36.0. Use the upstream checker in check mode on each one-file contribution and its expanded statement; run the command from a checkout that contains the named statement file:

    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35GuardedPoolTraceBound.lean research/statements/PlaneCase35GuardedPoolTraceBound.txt check
    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35ThreeFreeGateReduction.lean research/statements/PlaneCase35ThreeFreeGateReduction.txt check
    node tools/check-lean.mjs lean/PEqualNP/Research/PlaneCase35FourOmissionCost.lean research/statements/PlaneCase35FourOmissionCost.txt check

- PlaneCase35GuardedPoolTraceBound — ACCEPTED (check), exit 0; 2,155 kernel constants. [Single-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/452fe2617df71cd9f8d417e86c4439f0fe6427e9...cf7152b71b9174c1523b99a44cf4cf6de80ce397).
- PlaneCase35ThreeFreeGateReduction — ACCEPTED (check), exit 0; 1,829 kernel constants. [Single-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/452fe2617df71cd9f8d417e86c4439f0fe6427e9...cdaf06a5804354084a58f235642e13a645e72ba3).
- PlaneCase35FourOmissionCost — ACCEPTED (check), exit 0; 1,822 kernel constants. This file proves the arithmetic bound of 206 for the packed tables by checking every triple and summing four triple inequalities. [Single-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/452fe2617df71cd9f8d417e86c4439f0fe6427e9...5bd633a9676442d3390fa86fe3ccaa0eb0f4019b).

Each manifest matched exactly one research source and 87 upstream definition modules. Independent expanded-statement compilation and pinned leanchecker replay passed for all three files. The two circuit theorems use propext, Quot.sound and Classical.choice; the cost theorem uses propext and Quot.sound. Early drafts needed a corrected cardinality-helper partition and finite-index case split before the reported accepted versions.
