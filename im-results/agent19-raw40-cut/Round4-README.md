# Raw40: exact local weighted maximum 334 for 0LA/1LB

**Established theorem (locally compiled, original accepted dependencies):** for the partial machine
`1RB0LA_1RC1LB_0RD---_1LD1LA_------_------`, every compatible completion satisfies `WeightedBound 334` and a compatible witness attains 334. This covers all 25^5 = 9,765,625 assignments, including all halt choices, via the canonical quotient branch soundness theorem. The accepted source semantics are those of the pinned canonical77 artifact 14997966221, and the exact original blobs of CanonicalPartial.lean (0542d92dfb937b630dfd24d11983aa3c826e911a), Agent46AutoPump.lean (9fb5e24599f4037123dc87d4e722f400eccabf6b) and enumerate_canon.cpp (edf5720193e89f861b3aa289273be396ea909efe). All 24 child shards, the residual-empty aggregate `Raw40C0LA1LB.all_quotient` and `all`, and `Raw40Round4Exact.lean` were compiled with Lean 4.36.0-rc2, using kernel decision procedures, and print only [propext, Classical.choice, Quot.sound] or a subset. No new CI run or global roster decrement is claimed.

The attaining machine is `1RB0LA_1RC1LB_0RD0RE_1LD1LA_0RF1LB_0RDHHH`: exactly 333 ordinary steps, then halt, delay zero. Thus 334 is the *exact* weighted bound, not merely a conservative threshold. `BB6.Agent19Raw40.Raw40C0LA1LB.exact_weighted` establishes both sides.

## Proof decomposition

The original enumerator yields 399 split nodes, 6638 cycle leaves, 2162 final-hole leaves and 374 FAR/pumping leaves (representative counts, not raw-table counts). The 374 are covered by 349 FAR witnesses and 25 exact pumping recurrences. Every generated proof is checked independently of the candidate finder. The compact pumping data `round4-pumps.jsonl` includes the explicit transition tables and symbolic block transfers.

The last difficult leaf was `1RB0LA_1RC1LB_0RD1RE_1LD1LA_1RA0RF_---0RB`. In the zipper convention, define C(n) = (A, [], 0111000 (111111111111)^n 1110111). Blank entry at step 57. For every n, exactly 224n+322 ordinary transitions take C(n) to C(n+1), without reading the unspecified F0 transition. Four right sweeps cost 20 each per 12-bit block and four left sweeps cost 36 each. Intervening fixed segments have lengths 12,15,43,20,52,25,61,36,58. Therefore all compatible completions are nonhalting. The generic search initially failed because its symbolic primitive-step budget was too small, not because a nested count was required.

## Reproduction

Using the accepted artifact on LEAN_PATH and Lean 4.36.0-rc2, compile the original Agent46AutoPump.lean and CanonicalPartial.lean, then:

```sh
python3 emit_autopump.py round4-pumps.jsonl BB6.Agent19Raw40.Round4 > Raw40Round4Pump.lean
lean -o Raw40Round4Pump.olean Raw40Round4Pump.lean
python3 prepare_round4.py
# Include this directory and round4/0LA_1LB/shards on LEAN_PATH.
cd round4/0LA_1LB/shards
lean -o Raw40C0LA1LBBase.olean Raw40C0LA1LBBase.lean
for f in Raw40C0LA1LBKid*.lean; do lean -o "${f%.lean}.olean" "$f"; done
lean -o Raw40C0LA1LBAll.olean Raw40C0LA1LBAll.lean
cd ../../..
lean -o Raw40Round4Exact.olean Raw40Round4Exact.lean
```

The prepared sharded source is intentionally regenerated; it is approximately 580 KB. Compile sequentially on low-memory workers: two large children can exhaust a 4-GiB cgroup. The proof consumes the exact same existing canonical checker; no extra axioms or trusted candidate classification. Next: integrate with the exact retained complement of the Raw40 parent, which remains unresolved.
