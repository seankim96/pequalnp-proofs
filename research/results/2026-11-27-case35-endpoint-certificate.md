# L-meta-2625, case 35: endpoint certificates and a 13-flag cut

Starting point: research commit cf0c096f8ed9c164c160d30f1aea46ac4ba64ec5. The checked upstream revision was 881a37ee4442bc7ba0ba4fe3d086a8ae0cfed2a9, with Lean 4.36.0. The desk returned not_open for L-meta-2625. The public tree contained R_meta_2625_50, R_meta_2625_317 and R_meta_2625_487 and no unrestricted certificate was identified. All four account PRs were merged. PRs #7762 and #8170 have accepted checker comments and no outstanding review changes. The fork branches were inspected before work. There was no lease to renew or release.

All row indices below are zero-based. The baseline four gates are OR(0,1), OR(3,9), AND(15,27), AND(17,26). The example fixes gates 5 and 6 to AND(13,26), AND(13,27).

## A suffix bound that survives thirteen omitted positive flags

PlaneCase35ThirteenFlagSuffix proves that a separating suffix still requires nine AND gates for any starting pool satisfying this condition: at each active positive outside {0,1,2,3,5,6,7,9,15,16,22,33,42}, the signal admits an active baseline wire whose negative support it contains. Disjunction preserves the condition. Any extra signal silent outside those thirteen flags also satisfies it. Every one of the 32,896 unordered pairs of the retained 257 negatives has a witness outside all thirteen flags at once. The proof imposes no condition on the suffix gates or output other than separating all 520 tests. The statement assumes this pool condition; it does not assert it for every circuit.

PlaneCase35EndpointSurvivors proves that removing the union of the 16 endpoint buckets associated to subsets of any four distinct ordered high flags leaves at least 262 of the 468 negatives. The bucket encoding has 1,932 nonempty keys and 3,812 distinct (key,endpoint) memberships. This cardinality theorem by itself does not connect each remaining negative pair to its witnessing positive.

| One-file Lean theorem | Official checker in check mode | Fork comparison against upstream revision |
| --- | --- | --- |
| PlaneCase35ThirteenFlagSuffix | ACCEPTED, 2,036 constants | [one file](https://github.com/seankim96/pequalnp-proofs/compare/881a37ee4442bc7ba0ba4fe3d086a8ae0cfed2a9...f87f34e2683bad5dadb8a282dcf560a8130386ac) |
| PlaneCase35EndpointSurvivors | ACCEPTED, 1,832 constants | [one file](https://github.com/seankim96/pequalnp-proofs/compare/881a37ee4442bc7ba0ba4fe3d086a8ae0cfed2a9...8d00cd585fe04aff319ba949d622ca720420740b) |

Both proofs use only propext, Quot.sound and Classical.choice. The checker invocation from the upstream checkout is `node tools/check-lean.mjs lean/PEqualNP/Research/NAME.lean research/statements/NAME.txt check`, with the named research files available.

## Two independent time-bounded searches

Each fixes the first six gates above and four further gates, leaving 53 free binary monotone gates. Each starts with all 52 positives and negatives numbered 0, 1, 2 and 234. A decoded candidate must pass all 520 rows. The budgets are per invocation of the CEGIS loop, using CaDiCaL from the pinned distribution.

| Gates 7 through 10, in order | Required suffix AND / OR | Initial variables / clauses | Seconds | Observed verdict |
| --- | --- | --- | --- | --- |
| AND(0,17), AND(0,23), OR(1,10), AND(14,34) | 9 / 18 | 16,960 / 543,096 | 90 | UNKNOWN, 56 rows, 0 decoded candidates |
| AND(2,14), AND(4,14), AND(10,14), AND(10,23) | 9 / 19 | 17,013 / 543,202 | 120 | UNKNOWN, 56 rows, 0 decoded candidates |

Reproduce with `research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27`, adding the four gates via --seventh through --tenth, and `--all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --seconds SECONDS --solver /path/to/pinned/cadical`. Five dispatch checks covered the cut, both orders of the fixed gate pair, and a mixed suffix. Neither run proves UNSAT.

## Every negative pair has a certified local witness

PlaneCase35LocalPairCertificate passed the upstream checker (2,009 kernel constants, propext, Quot.sound and Classical.choice). The theorem connects the numeric mask to the actual 30 baseline wire evaluations. Each of 109,278 pairs i < j either admits five distinct valid high-flag witnesses, or has a label of j all of whose set bits denote valid witnesses. A label may be empty, so the second alternative needs the endpoint membership argument before it can be used to infer separation. Independent replay gave 90,764 five-witness pairs and 18,514 remaining pairs. It decoded all 213,053 empty-through-four-flag bucket positions and all 3,812 endpoint memberships. Run `python research/order3_case35_endpoint_replay.py`.

The standalone source, exact expanded statement and verifier manifest were checked for each of the three lemmas. Each manifest listed one research module and the same 87 upstream definition source digests. [One-file local-pair comparison](https://github.com/seankim96/pequalnp-proofs/compare/881a37ee4442bc7ba0ba4fe3d086a8ae0cfed2a9...b4401821bfcfe3457848aacea6cb4f1c21b63284).

For an explicit 15-gate prefix, append to the fixed six the nine ANDs on physical wire pairs (2,14), (4,14), (10,14), (3,15), (12,16), (0,17), (6,18), (8,21), (10,23). Each accepts only its corresponding omitted positive and none of the negatives. Thus the thirteen-flag theorem requires nine more ANDs. No OR occurs after gate four in this prefix, so the previously verified nineteen-OR suffix requirement also still applies. This particular prefix needs at least 43 gates in total (15 + 9 + 19).

## The three-free-gate circuit bound is proved

**PlaneCase35ThreeFreeGateBound** closes the finite premise left at cf0c096. For all choices of up to four omitted positives, pad their high part to a quartet. Of the 468 negatives, at least 262 survive after all sixteen subset buckets are removed. For each surviving pair, five distinct witnesses cannot all lie in the quartet. In the endpoint-label case, if all its witness bits lay in the quartet then its higher endpoint would have been removed. The proof validates all 3,812 mask/slot records on the concrete data. It then applies the existing pair-separation argument. Whichever way gates five and six are ordered, and whatever the types and dependencies of gates seven through nine, any further suffix that separates the 520 rows contains at least nine AND gates. This is a lower bound on the suffix of these fixed-six-gate families, even when the output may select an earlier wire. The unrestricted 63-gate verdict is still open here. With sorted operands allowing repetition, the two base orders and three free slots give 2,819,900,160 syntactic encodings.

Official pinned checker: ACCEPTED (check), 2,507 constants, propext, Quot.sound, Classical.choice. [Single-file comparison](https://github.com/seankim96/pequalnp-proofs/compare/881a37ee4442bc7ba0ba4fe3d086a8ae0cfed2a9...7381e18c70f7b94156bc549216f80800a02b45ec). An initial draft using a binary-search decoder reached the machine memory limit without a verdict. The accepted one-file version uses a two-level table lookup whose entries are checked in Lean. An independent, slower numeric pair-table draft also hit the memory limit. Its output was not used as a proof.

A third CaDiCaL run exercised the new unrestricted-ninth cut. After the six fixed gates, set gates 7–9 to OR(0,2), OR(15,25), AND(32,33). Gate 9 reads both prior outputs and accepts positives 8, 48 and 49 and 48 of the negatives. Of 63 total gates, 54 are free, with at least 9 AND and 17 OR. There were 17,172 variables and 553,234 initial clauses on the same 56 seed rows. With a 90-second budget the actual verdict was UNKNOWN, with zero decoded candidates. The ninth-gate cut applies to all ninth-gate operands for the two certified sixth-gate orders.
