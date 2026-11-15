# Agent 42: general TM63 reset-index identity proved

The previously missing general-`L` reset-index algebra is now in
`im-results/agent24-champion-time/ChampionModular.lean` as
`BB6ChampionArithmetic.resetIndex_eq_pow_sub`:

```lean
resetIndex_eq_pow_sub (L a : Nat) :
  resetIndex L a = 2^(L+a+2) - 2^a - 1
```

The proof unfolds the exact existing definition
`(4 * 2^L - 1) * 2^a - 1`, applies `Nat.sub_mul` and
`Nat.pow_add`, and closes the exponent association arithmetically.
I reconstructed the current source module, inserted the theorem, and
compiled the resulting complete module with Lean 4.36.0-rc2. The
`#print axioms` result is `[propext, Quot.sound]`; no `sorryAx`.

The itinerary note `im-results/agent42-champion-terminal/CoqHaltItinerary.md`
has been reconciled: this resolves the general closed-form identity
needed to reuse the same parameter-generic Rst1' macro at the second
section length. It does **not** prove the Rsts1_v2 source transition or
any additional blank-root moves.

Useful next integration: expose the root-specific consequence
`tm63Index2 = 2^(tm63Length1 + tm63MiddleSection.exponent + 2)
- 2^tm63MiddleSection.exponent - 1` in the root countdown module,
then use the generic `rst1Prime_counted_macro` only after the
complete Rsts1_v2 endpoint has been source-verified.
