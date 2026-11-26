# L-meta-2625 — case 35, the first OR following the four fixed gates

Parent research commit: 6c296c39aee76729b7f857bdd4f41c0add3157e4. Upstream at verification: b59e3eed2d304792fd308db0d315dfdb8b7fe51b. Toolchain: leanprover/lean4:v4.36.0.

The four fixed gates, in order, are OR(0,1), OR(3,9), AND(15,27), AND(17,26). Input wires are numbered from zero. All 52 positives and all 468 negatives in the parent checkpoint enter both theorem statements. Two constant wires are allowed in the Lean model, operands may be reused, and the output may be any wire.

## New lower bounds

- **PlaneCase35FifthOrCut.** Fix any fifth AND or OR whose operands are two of the 30 available wires, including equal inputs and both orders. Any correct continuation uses at least 18 OR gates strictly after gate five. The 1,800 choices are covered by one theorem.
- **PlaneCase35FirstOrFree.** Every correct continuation of the four fixed gates uses at least 19 OR gates. The first OR may be preceded by arbitrarily many AND gates. The prior result gave 18 ORs here. Together with the previous nine-AND result strictly after gate four, this gives at least 32 gates in total for this branch (four fixed, nine more AND, nineteen more OR). Each gate counts once. The 63-gate question is still undecided.

A cut selects one negative and 19 positive flags. A wire accepting the negative has empty support on this cut. For a wire rejecting it, its support comprises the selected positive flags it accepts. If all starting wires have support of size at most one, a correct suffix needs 18 OR gates. The proof bounds the size of the union of supports for any set of output wires by the number of wires selected plus the number of ORs used. This covers shared subcircuits.

Five cuts suffice. For the second theorem a signature records values on the 52 positives and five selected negatives. The four-gate pool and constants generate 109 distinct signatures under AND. Each of the 30 generators acts on each of the 109 signatures, giving 3,270 intersections. Associativity composes these actions for arbitrary AND-only circuits. For every signature except that of wire 13, some cut either accepts its negative or misses every selected positive. On that cut it can be ORed with any other certified signature at zero support cost. If both signatures are exceptional their OR has the same signature. Thus the entire pool just after the first OR has singleton-or-empty support on one common cut. It still needs 18 further ORs. A suffix containing no OR also contradicts the support bound.

## Checks

Both Lean files are self-contained apart from Mathlib. The comparison statements expand the wire, gate and test-row definitions. From the fork root with the repository's pinned toolchain and dependencies, run for each name:

    node tools/check-lean.mjs lean/PEqualNP/Research/<name>.lean research/statements/<name>.txt check

| Theorem | Project checker | Kernel constants rechecked |
|---|---|---:|
| PlaneCase35FifthOrCut | ACCEPTED (check), exit 0 | 1,768 |
| PlaneCase35FirstOrFree | ACCEPTED (check), exit 0 | 1,859 |

Each manifest listed the one research file and the 87 definition modules from upstream. Their SHA-256 digests were checked against the published source or pinned upstream tree. Both axiom lists contained only propext, Quot.sound and Classical.choice. An earlier implementation that tabulated every intersection of two signatures built but its checker process was killed (exit 137). The accepted version uses the 30 generator actions.

For an independent replay of the signature certificate, run:

    python3 research/order3_case35_first_or_closure.py

It enumerates 9,737 conjunction truth tables on the 520 labels, projects them to 109 signatures, and checks the generator, intersection and cut-selection tables against the Lean source.

## Two more gates — numerical limit of the 19-flag method

    python3 research/order3_case35_sixth_or_slices.py

Among 3,459,600 ordered pairs of fifth and sixth gates, 3,455,840 have a common 19-flag cut and the other 3,760 have an 18-flag cut. The latter are 940 distinct pairs of truth tables. For each negative, the 26 raw inputs have 19 zero coordinates, and every positive uses at least one. A 19-flag cut must pick one flag using exactly one distinct zero coordinate for each of these 19 coordinates. Exhausting these choices and testing the four fixed gate outputs yields exactly 55,296 compatible 19-flag cuts across the 468 negatives. None works for the 3,760 exceptions. One example is OR(0,2) followed by OR(13,25). This establishes a limit of this single-negative certificate by finite Python enumeration. Circuits using other reasoning or more gates remain possible.

## 63-gate synthesis

CaDiCaL 2.1.2, 26 inputs, unrestricted wire reuse, all 52 positives and negative indices 0 and 234 initially encoded. Every decoded candidate is checked against the full set of 520 labels before it counts as a witness. Wall-time budgets cover the CEGIS loop including DIMACS writes.

| Fifth gate | Free slots | Minimum suffix AND / OR | Initial variables / clauses | Budget | Verdict |
|---|---:|---:|---:|---:|---|
| OR(28,29) | 58 | 9 / 18 | 17,922 / 573,212 | 120 s | UNKNOWN, 56 encoded rows, one decoded candidate failed the full test |
| free | 59 | 9 / 19 | 18,231 / 583,212 | 180 s | UNKNOWN, 54 encoded rows, zero decoded candidates |

An earlier attempt at the four-gate run was interrupted (solver SIGKILL), with no solver verdict. The table reports the isolated rerun. The CNF threshold dispatch was also checked for five configurations: fixed four only (9/19), fifth AND (8/19), fifth OR (9/18), different fourth-prefix pair (9/18), and that different pair with a fifth OR (9/17). Reproduce with:

    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth OR 28 29 --operator-bounds --all-positives --seconds 120 --solver /path/to/cadical
    python3 research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --operator-bounds --all-positives --seconds 180 --solver /path/to/cadical

## Desk and handoff

The desk returned not_open for L-meta-2625. Main contained R_meta_2625_317, R_meta_2625_487 and R_meta_2625_50, and no direct positive or negative solution to the parent was found. PR #6074 titled L-meta-2625 was closed unmerged. All four existing seankim96 upstream PRs were closed. #7762 and #8170 were merged with ACCEPTED intake comments, and neither had review requests for changes. The five prepared L-meta branches and the research head were checked before starting. No standard lease was acquired, renewed or released, and no upstream PR was opened for these fork research statements.

A next open lemma is nine ANDs strictly after an arbitrary fifth AND on this four-gate branch. The previous fork run found 55 exceptional positive masks and at least 408 separated negatives for each. Of the 900 ordered fifth AND choices, 46 equal one of their parents on all 520 rows. Of the others, 718 accept no positive, 132 accept one and four accept two. All 900 fifth OR choices inherit each accepted positive from a parent. This session also tested a uniform route with `python3 research/order3_case35_two_flag_endpoints.py`: for each negative pair, use the set of positive rows contained in the union of the negatives on all 30 wires. For any fixed exact witness mask of size zero, one or two, at most 24, 24 or 6 distinct higher endpoints respectively occur. Deleting higher endpoints of pairs whose witnesses are contained in an arbitrary two-flag exception set discards at most 61 of 468 negatives, across all 1,326 choices (first worst pair: flags 8 and 17). At least 407 negatives remain. Even the loose sum 24 + 2*24 + 6 = 78 would suffice for the 257 needed by the AND lower-bound lemma. These endpoint counts have only been checked by Python. For a second free OR, the 3,760 exceptions above need a different argument from a single 19-flag cut.
