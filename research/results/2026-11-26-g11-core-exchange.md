# L-meta-2384 — G11 residual-cover exchange

Parent fork checkpoint d18df13c1b745970242c0546d8e61c62356e7185. Upstream checkout fbd09f373b3c1e0c6d23524c4d1e6cb8d41f97d3. The desk returned not_open for L-meta-2625 and did not distinguish a proof from a withdrawal. The previous L-meta-4653 lease belonged to another session. The next standard assignment was L-meta-2384. PRs 7762 and 8170 were merged, with no further action requested. The other PR by the fork owner was closed. There were no new prepared branch heads.

The target concerns a least top-form binary AND/OR circuit C for the 11-vertex graph G, with size at most 21 and at least two junk ANDs. Write U for Ustar, B for twice the number of centreless gates plus the number of junk gates plus the number of OR gates outside lam. The target budget is b = B - |U|, with |U| ≤ B < 2|U|. It asks for a minimum cover K of the graph after deleting U and a set of at most b vertices extending K to a full cover of G.

## Exact exceptional costs

Mask bits follow the order of the sixteen edges in the assignment; bit i deletes edge i. Among all minimum residual covers, minimize how many further vertices must be added to cover G. In each of the seventeen exceptional cases of upstream reduction R_meta_2384_1, every minimum residual cover contains vertices 0, 1, and 2. Outside these three vertices G has disjoint triangles (3,6,7) and (5,8,9) plus the disjoint edge (4,10), so any full cover containing the three costs at least eight. The witness table also supplies a minimum residual cover inside a full cover of size eight.

| Minimum residual size | Exact additions | Deletion masks (hexadecimal) |
|---|---|---|
| 5 | 3 | 8f00, af00, cf00, ef00 |
| 4 | 4 | af40, afc0, bf40, cf80, cfc0, df80, ef40, ef80, efc0, ff00, ff40, ff80 |
| 3 | 5 | ffc0 |

## Exchange and charging

A replacement J for K can preserve every original edge hit by K, even when the deleted set is unknown. Then J covers every residual graph covered by K. Search for J with at most as many vertices as K, nested inside a full cover T. All 2048 vertex sets have such a replacement with |T| ≤ 8 if K contains {0,1,2}, and |T| ≤ 7 otherwise. When K is residual-minimum, J must have the same size. Thus the added set T minus J costs at most that threshold minus |K|. In the reverse direction all full covers cost at least seven, or eight when they contain {0,1,2}.

The remaining circuit-specific condition asks for a residual-minimum K whose size plus b reaches this threshold. The graph computations impose no restriction on which circuits can realize a pair (U,B).

## Reproduction and budgets

Run `python3 research/g11_core_exchange.py` to enumerate all 2,048 vertex sets and 65,536 edge deletion masks. The subset dynamic program propagates the lexicographic minimum (residual size, additions, mask) from smaller to larger deletion masks. For 65,519 masks the best total is seven; for seventeen it is eight. A separate exhaustive check tests the replacement condition on all 2,048 vertex sets. This is an exhaustive finite computation with no search timeout. No 21-gate circuit synthesis or UNSAT claim is made. Initial development used Lean's bv_decide (default SAT timeout 10 seconds per invocation); the project checker rejected its native axioms. The final research sources instead use kernel-reduced finite cases.

G11Rare: ACCEPTED (check), pinned Lean 4.36.0, 1,889 kernel constants. The research-source hash and all 87 definitions hashes matched the checked source tree. The theorem quantifies over every nonnegative extension budget and all seventeen masks; it proves both feasibility at the indicated cost and impossibility below it.
