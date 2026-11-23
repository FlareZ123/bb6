# Agent 4 — episode-19 endpoint misses the external halting cylinder modulo 3

The current nineteenth terminal certificate states `t19 % 27 = 12`. The subsequent source packet in `BlankNineteenthRejoin.lean` has pure-unary output parameter

`a19 = 64*t19 + 113`.

Therefore `t19 % 3 = 0` and `a19 % 3 = 2`. The external TM62 halting cylinder is `C + 3^108*k`, with `C % 3 = 1`; every member of that cylinder is 1 modulo 3. Thus the episode-19 pure-unary reentry parameter is **not** in the accepted halting cylinder, for every (k\ge0). This is an exact endpoint exclusion, not a claim about intermediate primitive configurations or later root states.

A small Lean lemma can be added after `t19_mod27` is available:

```lean
private def haltingCylinderC : Nat :=
  1975700577069254261393123959451562008800234946348086

theorem t19_mod3 : t19 % 3 = 0 := by
  have h := t19_mod27
  omega

theorem root19_unary_mod3 : (64*t19+113) % 3 = 2 := by
  have h := t19_mod3
  omega

theorem root19_reentry_misses_cylinder :
    ∀ k : Nat, 64*t19+113 ≠ haltingCylinderC + 3^108*k := by
  intro k h
  have hmod := congrArg (fun n : Nat => n % 3) h
  have hC : haltingCylinderC % 3 = 1 := by decide
  have hp : (3^108*k) % 3 = 0 := by simp
  have hleft := root19_unary_mod3
  have hright : (haltingCylinderC + 3^108*k) % 3 = 1 := by omega
  omega
```

The numeric residues are also confirmed directly by exact integer arithmetic. This extends the endpoint table in `KnownCylinderReentryScreen.lean` from episodes 17–18 to episode 19 once the stage-4d certificate and stage-6 source reentry are accepted.
