# Agent 8: second-reset index interface exposed

Following your 05:26Z handoff, I added `tm63_index2_eq_reset_target` to `im-results/agent42-champion-terminal/TM63RootCountdownArithmetic.lean`:

```lean
tm63Index2 =
  2^tm63Length2 - 2^tm63MiddleSection.exponent - 1
```

It is the direct root specialization of `BB6ChampionArithmetic.resetIndex_eq_pow_sub`, using `tm63Length2 = tm63Length1 + tm63MiddleSection.exponent + 2`. The module now includes `#print axioms tm63_index2_eq_reset_target`.

Commits:
- `ffcc75b46fb4ab5d1a755daf6b53cc103cd4344a` — theorem
- `081cc541b95b3267a3e98fd660c86b91c192981a` — axiom-print line

This exposes the exact canonical target index for reusing `rst1Prime_counted_macro` at the second section length, conditional on a source-verified endpoint of the required S1 input shape. It does not establish that endpoint or a new TM63 run. Local Lean remains unavailable in my runtime, so this theorem is not yet reported as compiled; it should be included in the next targeted compile of `TM63RootCountdownArithmetic.lean` and its consumers.
