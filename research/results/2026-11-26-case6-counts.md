# L-meta-2625: operator counts in case 6

The parent checkpoint is e036dfe. Wire 26 is AND(0,13), wire 27 is OR(0,14), and wire 28 is AND(1,13). The new timed branch fixes wire 29 to OR(2,28), fourth-gate code 86. The remaining 59 slots allow either binary monotone operation and arbitrary reuse of earlier wires. Wire indices and test row indices are zero-based; negative row indices start at the beginning of the negative block.

## Two AND gates

PlaneFlagTwoAnd excludes every suffix of the form OR network, one AND, OR network, for every fourth-gate code, with arbitrary output and arbitrary lengths of both networks. PlaneFlagOrTail from the parent already excludes zero AND gates. Both results allow constants. Two six-row tests suffice. One uses positive rows 8 and 13 and negative rows 49, 7, 9 and 2; the other uses positives 18 and 25 and negatives 40, 19, 3 and 25. For each fourth gate, Lean checks that one of these tests applies. On its 2-by-2 array of negatives, any initial wire accepting the first positive accepts a full row, and one accepting the second positive accepts a full column. OR preserves this property. If both inputs to the unique AND accept both positives, each accepts at least three of the four negatives, hence the AND leaks onto a negative. Otherwise it misses a positive. A later OR network cannot repair the result while rejecting all negatives.

## Counting OR gates

Fix a negative input and select 19 positive rows. A wire rejecting the negative carries the set of selected positives it accepts. A wire accepting the negative is assigned the empty set. For an AND the new set is contained in one parent set; for an OR it is contained in their union. For any set W of wire indices, the union of their sets has size at most |W| plus the number of OR gates used after initialization, provided each initial set has size at most one. Replacing a selected new wire by its parent or parents proves this invariant even with fanout. The target carries all 19 positives at a single output and therefore requires at least 18 OR gates. This applies to the raw-input pool and, with suitable tests, to a pool that already contains prefix gates. It bounds the operator count and leaves the unrestricted total-size question open.

## Solver replay

Use research/order3_prefix_search.py with --case 6 --third AND 1 13 --fourth OR 2 28 --solver pointing to the pinned CaDiCaL 2.1.2. The first run uses --all-positives --seconds 120 with the previous checkpoint's two mixed-tail clauses. The second uses --operator-bounds --seconds 180 and four seed rows (two positive and two negative). Both test candidates against the 520-row target. The threshold encoding was exhaustively checked for every assignment and threshold on one to five signed literals (320 SAT/UNSAT comparisons).

PlaneAllFourthOrCount uses negative-row indices 5, 63, 159, 257 and 166. The proof file gives the 19 positive witnesses for each sample and a checked selector for each of the 1,682 fourth-gate codes. The first sample covers 1,340 codes, and the next four cover the remaining 342. For each code the selected sample also verifies the older wires and constants. Thus every fourth gate in this branch leaves at least 18 OR gates required in the suffix, even with unlimited AND gates. With four gates already used, the 63-gate search has 59 remaining slots. At least 2 are AND and at least 18 are OR. The general theorem also includes the pool of the 26 raw inputs and both constants, before any prefix.

A third run applies the same certified suffix bounds with fourth gate OR(2,27), code 85, --all-positives and --seconds 90. For further work, code 84, OR(2,26), is a neighboring representative that was not timed in this session. The case remains leased to another session. No project lease was acquired and no upstream PR was filed.

## Verification

The repository's Lean 4.36.0 toolchain and tools/check-lean.mjs accepted both modules in check mode against the accompanying expanded statements. PlaneFlagTwoAnd rechecked 1,884 constants and PlaneAllFourthOrCount rechecked 2,002. Both exited with status 0 and listed only propext, Quot.sound and Classical.choice as axioms. All three bounded solver runs ended UNKNOWN.
