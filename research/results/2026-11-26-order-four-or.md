# L-meta-4653: OR complexity of the order-four incidence function

Parent research checkpoint 30bab810cd6b0aa9973e43302293033b5accfe88. On 26 November 2026 the desk returned not_open for L-meta-2625. The upstream tree b9979b6899c4c4b4c0ceaaf6155681062bc9e2bd still contained its three reductions and no direct final proof file. Closure alone gives no mathematical verdict for the 63-gate question. PRs 7762 and 8170 were merged; the prepared fork branches had no new heads.

The next standard lease was L-meta-4653. There are 21 points and 21 lines. A point p meets a line l when their cyclic difference lies in {0,5,7,17,20}. The input is any subset of the 42 vertices and the output detects a selected incident pair. The desk asks for at least 104 OR gates in any binary monotone circuit satisfying a bypass irredundancy condition. The weaker unrestricted bounds below permit arbitrary wire reuse, unbounded AND counts, and gates of arity at most two.

## Vertex-cover certificates

A maximal independent input with point mask 0x185 and line mask 0x50c00 leaves 34 individually sensitive coordinates. Its complement is a vertex cover. Each of its 34 centers has an edge to the independent set. Select one such private edge per center; each starting star in this cover meets at most one selected edge. Apply the simulation in upstream L-meta-8265. It gives one program of binary edge-set unions with downward closure, valid for every cover, of length at most the circuit's OR count. In a backward derivation of required sets, expanding one instruction can increase the number of required sets by at most one even if several requested subsets use it. Thus reaching all 34 private edges from this cover needs at least 33 union instructions.

A refinement uses seven translations (offsets 0,3,6,9,12,15,18) of the cover and its private edges. If either operand of the first instruction is unavailable on one of these covers, that instruction is inactive there. Otherwise each operand can contain at most one incident edge: two distinct incident edges have at most one common endpoint and some cover omits that endpoint. One can choose a translation whose private-edge list misses the left operand's single edge. Under that cover the first instruction still supplies sets hitting at most one sample each. Reaching all 34 now requires at least 33 more instructions.

## Reproducible finite census

Compile research/plane_four_independent_covers.cpp with a C++20 compiler and -O3. The replay exhausts all 2,097,152 point subsets, determines the largest compatible line set for each and checks maximality on the point side. The smallest maximal independent sets have eight vertices, and there are 105 of them. Histogram (size, number): (8,105), (10,16800), (11,5460), (12,2408), (14,420), (17,42), (21,2).

For all 741,321 ordered pairs of raw-input OR gates (each gate reads two distinct inputs), at least four of the 105 independent baselines turn on both gates. The triple OR(0,1), OR(0,2), OR(21,28) has no such common baseline. These census results are numerical. No SAT/SMT solver was used; no SAT/UNSAT verdict is claimed.

## Restricted 104-OR counting argument

Allow a shared network of binary OR gates to build variable subsets, take k ANDs of pairs of such disjunctions, then OR the k terms. An exact cover of the 105 incidences can use only stars, because distinct centers have at most one common neighbor. Any shared input OR that builds a multi-vertex subset of a center's neighbors can be charged to at most one center. Charging all leaf sets together by center bounds the 105 covered edges by the number of network ORs plus k. The final aggregation costs k-1 ORs. The matching construction uses four line-neighbor ORs per point, one AND per point, and 20 outer ORs (84+20 OR gates). Extending the argument to arbitrarily alternating circuits remains the missing structural step.

## Replay and check scope

Use the pinned leanprover/lean4:v4.36.0 and the repository's tools/check-lean.mjs in check mode, with the corresponding research/statements/<module>.txt. Overlay the research sources on upstream b9979b6899c4c4b4c0ceaaf6155681062bc9e2bd for the published circuit-to-union simulation L_meta_8265 (source SHA-256 99bbd792fa0a41594434de72d75e462db1470379c646389ffce8d09294a097dd). The finite search budget was exhaustive over 2^21 point masks, 861^2 ordered pairs of raw ORs, and the one specified triple. The C++ replay also reconstructs the seven private-edge samples, checking coverage of all 42 omitted vertices and the empty intersection of the seven samples.

PlaneFourSharedStars: ACCEPTED (check) for the restricted shared-OR/AND/final-OR model, 1,797 kernel constants. The research module hash and all 86 definition-module hashes match the local checked sources. This is a local research theorem with its own exact statement. The desk's unrestricted 104-OR statement remains unresolved in this run.

PlaneFourFirstJoin: ACCEPTED (check), 2,093 kernel constants. The manifest covers both the base counting proof in PlaneFourCoverCount and the seven-cover first-instruction refinement. All two research hashes and 86 definition hashes match. The exact checked implication says that a single union program that works on every vertex cover must contain at least 34 instructions.
