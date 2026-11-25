# L-meta-2625, fourth gate after AND(1,13)

Resume from b1c16b7. Case 6 fixes wire 26 to AND(0,13) and wire 27 to OR(0,14). Fix wire 28 to AND(1,13). A fourth binary gate receives two ordered operands from wires 0 through 28. Its code is 29a+b for OR and 841+29a+b for AND. The search allows shared wires throughout the remaining DAG.

PlaneFlagFourth covers all 1,682 codes on the 52 positive and 468 negative test rows. An old wire or a renamed member of the 100-entry roots array dominates each candidate. A dominator keeps every true positive of the candidate and adds no true negative-row output. The 12 prefix-preserving renamings fix raw wires 0, 1, 13 and 14. Enumeration found 775 distinct signatures, 455 columns undominated by old wires and 448 maximal columns before renaming.

PlaneFlagOrTail excludes every OR-only continuation after every fourth gate, at any length and any output index, even with constant wires available. For at least one of positive rows 8 and 13, every wire accepting that row also accepts some negative row. This property survives OR. PlaneFlagAndTail excludes every AND-only continuation. Each wire accepting all 52 positives also accepts negative row 0, and this implication survives AND. The two lemmas allow the search to require both operators among the 59 free slots for a 63-gate candidate. They do not settle the mixed suffix.

Run research/order3_prefix_search.py with --case 6 --third AND 1 13, the indicated --fourth arguments and --seconds, and --solver pointing to the pinned CaDiCaL 2.1.2 binary. For the first two experiments add --no-tail-pruning. Only the first experiment uses --all-positives. Every decoded candidate was compared with the full 520-row test set. The exact budgets and outcomes are in the adjacent TSV. Timeouts remain UNKNOWN.

All three Lean modules have independent expanded theorem statements in research/statements for tools/check-lean.mjs in check mode. The public desk already showed this assignment as leased, so this checkpoint is fork research. The unrestricted mixed-gate question remains open. For a fresh follow-up, OR(2,28), code 86, is among the retained fourth gates and was not timed in this session.

Pinned Lean 4.36.0 and the repository checker returned ACCEPTED (check), exit 0, for PlaneFlagFourth (1,824 constants rechecked), PlaneFlagOrTail (1,844) and PlaneFlagAndTail (1,847). This is local project-checker verification on the fork. The SAT runner was also checked to emit both 59-selector clauses on this full-row branch and omit them for the reduced-row experiment and the opt-out flag.
