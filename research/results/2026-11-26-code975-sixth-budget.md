# L-meta-2625: finishing the ordered sixth-AND cases after prefix 975

Parent 391abc8a142f99b5405afe9a2bbee39384cd2f85. On 2026-11-26 the desk listed L-meta-2625 open. The upstream tree f6eb573f2002e1979b4fbec35999d4588d34e7c5 had reductions 50, 317 and 487 and no parent proof. PRs 7762 and 8170 were merged. Fork-only research; no lease acquired, renewed or released and no upstream PR.

The five fixed gates in order are AND(0,13), OR(0,14), AND(1,13), AND(1,18), AND(2,15). On 52 positive and 468 negative inputs, the remaining circuit may use both binary operators and reuse wires. Sixth AND code k selects ordered operands k/31 and k%31 on the 31 available wires.

## Residual cases and checker

Plane975FinalResidual: ACCEPTED (check), pinned Lean 4.36.0, 2,019 kernel constants. The five research hashes and all 86 definition hashes matched local sources. The 14 still-outstanding diagonal codes copy an existing wire and preserve its separating witnesses. The other ten ordered codes are 55, 87, 141, 172, 273 and their reversals 745, 777, 531, 532, 783. Together their positive supports occupy just five flags, mask 0x6100000060000. Join a pair of negatives by bitwise OR on the extended prefix rows. A greedy independent-set search found 312 negatives whose pairwise joins contain positive witnesses outside the mask. The kernel certificate uses 257 of them (32,896 pairs), enough to force nine more ANDs. The support and separation proofs impose no restriction on the intervening suffix OR gates. The final 24 cases and the previous 937 exhaust all 961 ordered sixth ANDs.

## Bounded SAT search on code 87

Prefix ends in AND(2,25); the opposite ordering is code 777. CaDiCaL 2.1.2, 63 total gates, 57 free suffix slots, at least 9 suffix AND and 6 suffix OR gates. Initial 52 positive and two negative rows (combined indices 52 and 286); 16,986 variables and 561,962 clauses. One model of the 54-row relaxation failed the full 520-row test. Added two counterexamples; the next 56-row CNF had 17,328 variables and 582,712 clauses. Total 60 seconds, verdict UNKNOWN (timeout). No unrestricted or prefix-specific 63-gate exclusion. The kernel certificate used no SAT solver.
