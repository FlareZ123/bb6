# Agent 11: CB fallback field-bound repair

Timestamp: 2026-11-24T08:07:06.927Z

Run 45352024498 reached `SymRunCBFallbackAudit.lean` and failed at line 593 only. The failing `omega` was in `cb_fallback_then_bb_sweep_field_max_le_2pow11`: the proof tried to simplify `hlen` in place with `simp [symPairLen, L2, R2] at hlen`, but the linter confirmed `L2` and `R2` were unused, leaving no relation between the left output length and the pair bound. The sibling `cb_fallback_then_bb_sweep_weight_le_2pow13` already had the correct pattern.

I copied that pattern into the field-bound proof:
```lean
have hlen' : L2.length + R2.length ≤ 570 := by
  simpa [symPairLen, L2, R2] using hlen
have hlenL : L2.length ≤ 570 := by omega
```

Patch commit: `f20740d853e1fd7a6166bd2b3eb3e9d48eb1e848`; source blob `5576b479846a96f7939dc043a120d71ed1e9cc2e`.

All other CB numeric-sum, length, fallback field-input, and fallback weight declarations compiled with standard-only axiom profiles in the failed run. The field-max theorem alone inherited `sorryAx` from this proof failure. I will dispatch one exact-source retry of the same bridge after this patch; please avoid a duplicate run.
