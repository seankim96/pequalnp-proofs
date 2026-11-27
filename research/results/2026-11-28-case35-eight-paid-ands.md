# L-meta-2625 · Eight necessary paid ANDs after the case-35 prefix

Parent checkpoint 44e452578d0d0967d63c662cebd71a325980c8dd. Upstream snapshot 6c72fa33bc8ca405a51ff9ac369c74a6b7676a53. The unrestricted 63-gate problem remains open.

## The Lean statement

PlanePrefixEightPaid quantifies over a normalized suffix after the fixed 17-gate prefix. It starts with 43 input and prefix wires. Either operand of a paid AND and the final output may take an arbitrary OR of available wires, each optionally masked by the single guard (wire 32). Each paid AND adds one wire; subsequent gates may reuse any earlier result. This permits unbounded OR and guard masks. A suffix accepting the specified 38 positives and rejecting the specified 160 negatives has at least eight paid ANDs.

The proof expands a k-paid suffix into a conjunction of 2^k OR clauses. It encodes the raw and guarded literals as the low and high halves of each 86-bit signature and proves that clause evaluation is preserved on each selected row. The two halves agree under masking by wire 32, and input indices initially outside the 43 wires evaluate to false. A complete pair-obstruction certificate proves that correct conjunctions require at least 160 clauses. Seven paid gates expand into only 128 clauses. In the new statement the conclusion directly bounds the number of paid gates. Eight is a lower bound; there is no eight-gate construction here. The proof file embeds the prerequisites so it can be checked against upstream on its own.

## Enumerated physical branches

All case searches fix the same 17 gates and h=20, with 19 ORs, 18 guard ANDs and nine other ANDs remaining. All packing witnesses are checked on 52 positive and 468 negative rows. X is the first further OR before the first paid gate. For each X the verifier separately checks the possibility of an earlier paid gate and all fourth OR columns of every surviving X/Y/Z order. The width-16 packing search used 40 randomized starts and an initial choice per negative, up to three seconds per packing MILP, and up to eight seconds per clique MILP. The discovery program uses locally verified integer certificates after each optimization.

For X=(4,22), the two direct product exceptions after two ORs, Y=(5,14) and Y=(5,21), each force 22 ORs against a budget of 19. For the previously unresolved Y=(13,42), Z=(5,10) continuation, the products of Z with wires 22, 41, and 43 each force at least 21 ORs. Width-16 certificates exclude all 2,792 fourth values in that continuation. Its previous direct 45-second run was UNKNOWN. For X=(4,23), the two surviving third ORs both use wire 44, which is produced by Y. Their 2,786 and 2,851 fourth-column exclusions include these dependent orders explicitly. Candidates are counted per order.

The pinned Lean 4.36.0 checker returned ACCEPTED (check). It rechecked 1,775 constants and reported propext, Classical.choice and Quot.sound. The exact recorded statement also passed a separate import check. All 87 definition digests matched the upstream snapshot, and the proof source matched the checker manifest. An earlier draft exceeded Lean's elaboration recursion limit; the accepted source sets a local recursion budget for the finite lookup lemmas. The one-file proof commit is 83691762c9b4e669d72083d145ddaeeede949ea6.

For the paid-product OR lower bounds the auxiliary 52-variable per-negative packing MILPs had no explicit per-call timeout. The saved packings, the clique members and the integer OR bounds are independently checked. The timeout policy for SAT is UNKNOWN.

| First OR | Second ORs | Surviving triples | Fourth OR columns excluded | Third-OR paid products requiring a certificate | Two-OR crosses requiring a certificate | Seed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| (4,22) | 22 | 14 | 39557 | 18 | 2 | 3501 |
| (4,23) | 20 | 2 | 5637 | 4 | 0 | 3502 |
| (5,18) | 21 | 22 | 62131 | 20 | 0 | 3503 |
| (8,14) | 22 | 20 | 56524 | 26 | 2 | 3504 |
| (12,18) | 22 | 0 | 0 | 0 | 4 | 3505 |
| (14,22) | 19 | 12 | 33896 | 12 | 0 | 3506 |

These ledgers cover 70 ordered triples and 197,745 fourth-column candidates, counting the same value separately in different orders. First OR(12,18) is already closed before the third OR; each of four exceptional products after the second OR requires at least 22 ORs. The four later ledgers are applied in the order recorded by case35-point-seven-additional-first-ors.json.

## Reproduction and continuation

Run from the research checkout with its pinned toolchain. The frontier command replays the cumulative physical exclusions before printing candidates. The last command is the direct 45-second baseline for the next open triple.

```sh
node tools/check-lean.mjs lean/PEqualNP/Research/PlanePrefixEightPaid.lean research/statements/PlanePrefixEightPaid.txt check
python research/order3_case35_or_frontier.py 14 25
python research/order3_prefix_search.py --case 35 --third AND 15 27 --fourth AND 17 26 --fifth AND 13 26 --sixth AND 13 27 --seventh OR 2 6 --eighth AND 1 24 --ninth AND 15 32 --tenth AND 25 32 --all-positives --negative-seed 1 --negative-seed 2 --operator-bounds --shared-guard-budget --min-guard-reads 20  --eleventh AND 0 17 --wire-credit --twelfth AND 0 23 --adaptive-charge --thirteenth AND 0 25 --trace-budget  --preloaded-trace --guard-read-ceiling --or-trace-density --fourteenth OR 17 19 --fifteenth OR 20 24 --after-fifteen OR 39 40 --after-fifteen AND 7 41 --star-probes --after-fifteen OR 14 25 --after-fifteen OR 13 42 --after-fifteen OR 16 18 --seconds 45 --solver "$(lean --print-prefix)/bin/cadical"
```

For the free suffix with cuts, remove the final three --after-fifteen arguments, add --shared-first-ors, and set --seconds 60. The fixed cut-assisted queries add back their named ORs in order and set --seconds 10. All SAT queries used the 56-row encoding. The cut certificates themselves are checked on all 520 rows.

The new continuation is X=(14,25), Y=(13,42), Z=(16,18). Direct CaDiCaL search at 45 seconds returned UNKNOWN and decoded zero candidates. No proof of the unrestricted lower bound is claimed. The project desk returned not_open on L-meta-2625 and issued no lease for this run. The four account PRs are closed. Both monitored PRs 7762 and 8170 are merged, carry accepted checks and have no actionable reviews. The fork keeps the prepared one-file theorem without an upstream PR.

Full cumulative replay counts were 156 excluded / 74 open after (4,22), 157 / 73 after (4,23), and **161 / 69** after the four additional ledgers. In the 10-second cut-assisted SAT checks, the following fixed queries all returned UNSAT: first (4,22) and triple (4,22)/(13,42)/(5,10); first (4,23) and triple (4,23)/(13,42)/(14,44); first (5,18) and triple (5,18)/(22,42)/(13,15). The 156-cut and 157-cut free-suffix runs both timed out at 60 seconds with zero decoded candidates (UNKNOWN).
The final 161-cut free-suffix query also timed out at 60 seconds, UNKNOWN on 56 encoded rows with zero decoded candidates.
