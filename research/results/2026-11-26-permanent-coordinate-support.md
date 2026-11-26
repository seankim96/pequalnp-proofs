# L-gct-230 — four fixed coordinates on a 4 × 4 permanent level

The standard desk assignment asks whether an affine space through A = I + J (diagonal 2, other entries 1; J here denotes the all-ones matrix) on the complex permanent-65 level can have dimension six. This is a hard prove lease, with reductions closed. The unrestricted assignment is unresolved in this session.

## Restricted theorem

Let L be a complex linear subspace of 4 × 4 perturbations with permanent(A+t) = 65 for every t in L. If four distinct entries vanish identically on L, then dim L ≤ 5. Equivalently, a six-dimensional candidate must use at least thirteen of the sixteen coordinates. The four fixed entries are common to the entire space. The theorem allows arbitrary, correlated complex values in all other positions. It does not classify dense subspaces.

## Why the certificate works

Number the entries by 4i+j. Write g for the gradient and D for the Hessian of the permanent at A. Comparing the constant polynomial permanent(A+st) with its first and second coefficients gives g·t = 0 and tᵀDt = 0 for every t in L. The gradient entries are 16 on the diagonal and 11 elsewhere. For a pair of entries in different rows and different columns the Hessian entry is the permanent of the complementary 2 × 2 submatrix. Other entries are zero.

Border D by g to form the 17 × 17 symmetric matrix H with bottom-right entry zero. In this coordinate space W = L × ℂ is totally isotropic for H, by polarization. An integer matrix K satisfies H K = 8,090,940 I. For each of the 1,820 four-element subsets F of variable positions, K[F,F] is nonsingular. The four corresponding columns K[:,F] therefore span a four-dimensional space E. Pairing them against w in W multiplies the four frozen coordinates of w by 8,090,940, so E is orthogonal to W. Moreover E meets W trivially: evaluate any common vector on F and use invertibility of K[F,F]. Consequently 2 dim W + 4 ≤ 17, yielding dim L ≤ 5.

For the fixed-last-row special case, the thirteen-dimensional bordered Hessian on the twelve free positions plus the border has determinant 21,808,934,160. Its maximal isotropic dimension is at most six. This supplies a separate proof of the same bound for the original three-row case.

## Exact replay

Run `python3 research/permanent_coordinate_support.py`. The script differentiates all 24 permutation products over integers and computes the actual bordered determinants by fraction-free elimination with pivoting. There are no third-party dependencies. It enumerates all supports of the indicated sizes.

| Free coordinates | Supports | Singular bordered matrices | Distinct determinants |
|---|---:|---:|---:|
| 12 | 1,820 | 0 | 58 |
| 13 | 560 | 0 | 22 |
| 14 | 120 | 0 | 7 |
| 15 | 16 | 0 | 2 |
| 16 | 1 | 0 | 1 |

This computation uses no SAT/SMT solver or timeout. Over 13 free coordinates the bordered matrix has size 14, so the same dimension argument permits a six-dimensional level space. Higher permanent coefficients, or another geometric argument, are needed. A natural next case is exactly thirteen free coordinates, where the six-dimensional tangent plane saturates the quadratic bound. The cubic coefficient and its polarization must then vanish on this maximal isotropic plane. Over fourteen, fifteen, or sixteen free coordinates the present four-zero theorem also leaves the existence question open.

## Project state

Research parent 35860b73cd801c37ea06af6e9feda5949d4f9d36; upstream 10201e28a25974bce05e18608bead95851b1cdfc. The desk reported L-meta-2625 as not_open (proof or withdrawal unspecified); no unrestricted 63-gate verdict follows from that status. Upstream PRs 7762 and 8170 are merged with checker acceptance and no requested review changes. PR 26309, the earlier L-meta-2384 reduction, merged at d9d5772913661d9dd5c4b16f8c5e6f460e0c34ca. Its merge is not a proof of the circuit lower bound.

A second exact enumeration classifies two-entry directions. Nonzero first derivative coefficients force both entries to be nonzero in such a direction, in a unique ratio. The quadratic constraint forces their positions to share a row or a column. This leaves 48 lines. In their exact orthogonality graph there are 72 maximal cliques of two lines and eight of six lines. The latter are exactly the six pairs in each fixed row or fixed column, spanning its three-dimensional gradient kernel. Thus the span of all two-entry directions in a level space has dimension at most three. Varying just one row within its gradient kernel attains three. This clique enumeration is an independent Python result, outside the Lean statements.

## Checker and lease

Pinned Lean 4.36.0 and the upstream check-lean.mjs, in check mode on each standalone research statement. PermanentSupportMinors: ACCEPTED, 1,997 kernel-rechecked constants. PermanentThreeRows: ACCEPTED, 1,767. PermanentTwelveCoordinates: ACCEPTED, 2,088. All three research SHA-256 digests and all 87 upstream definition hashes matched the final manifest. The only recorded axioms were propext, Quot.sound and Classical.choice. The first, coarser integer certificate compiled but its verifier was killed (FAULT, exit 137). Splitting the certificate by two leading indices produced the accepted check. No SAT solver was used for this assignment.

The standard lease was issued to this run at 14:35 UTC, renewed roughly every five minutes and released as missing_lemma (desk HTTP 200). No upstream PR was opened for this restricted result because the lease disallowed reductions and the case with at least thirteen free coordinates remains unresolved.
