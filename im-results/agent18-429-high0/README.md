# Exact original-machine #429 high-zero J branch (all natural parameters)

Status: source-exact Lean 4.36.0-rc2 verification, [CI 42517987573](https://github.com/FlareZ123/bb6/actions/runs/42517987573) SUCCESS, no `sorryAx`.

The original #429 raw two-symbol six-state machine is `BB429PhysicalFrontier.target429`. Its exact canonical symbolic tape is `BB429JPhysical.jTape u w`. For every `u : Nat`, the theorem `BB429High0Physical.j_high0_to_junc_raw` in [High0Physical.lean](High0Physical.lean) proves:

```lean
∃ c', BB6Coverage.run target429 (4*u*u+28*u+110)
    {state:=A,head:=0,tape:=jTape u (2*u)} = some c' ∧
  Represents (junc 0 0 (4*u+12)) c' ∧
  c'.head = -((2*u+6 : Nat) : Int)
```

The full infinite tape is matched by the `Represents` relation; this is stronger than checking a bounded simulation. The lower-level [High0Source.lean](High0Source.lean) verifies the suffix from the exact C/B sweep endpoint in `18*u+85` raw steps with head delta `-(4*u+7)`. The independent published precursor `BB429JFirstBranch.j_c_sweep` accounts for the preceding `4*u*u+10*u+25` physical steps.

The suffix proof decomposes into an eleven-step source E/1 entry, an arbitrary-length E/1 reduction, the original E/1 revisit, repeated eight-step C/1 processing of `1101` blocks, and an E/1-to-Junc normalization. All phases are exact, quantifier-uniform, and separately compositional. Both source and physical results are audited by [.github/workflows/agent18-429-high0.yml](../../.github/workflows/agent18-429-high0.yml).

Scope: the starting J tape is a *synthetic prepared configuration*. No blank-root reachability is asserted, and no halting/nonhalting theorem or BB(6) value follows. Together with previously certified J outer cases and high-two, this closes one formerly simulation-only neighboring J branch.
