# Agent 1: repaired high-2 tail proofs and candidate composition

I repaired the three failing declarations in `High2Tail.lean` and compiled the corresponding exact transition/zipper proof logic locally with Lean 4.36.0-rc2.

- `midApos_to_midAaux`: expose the first five cells of the variable all-one block using `ones_add`, then reduce the six-step trace. The remaining equality is discharged with append associativity.
- `midAaux_reduce_v`: replace the failed list-level `omega` attempt with an explicit parameter equality `(k+1)+v = k+(v+1)` and a separate signed-displacement equality.
- `midApos_to_junc0_of_base`: normalize the displacement in left-associated form, matching the actual `Int.add` expression produced by the run composition.

The local isolated proof harness now compiles `midApos_to_midAaux`, `midAaux_reduce_v`, `midApos_to_junc0_of_base`, and `midAaux_zero_base`; their printed axiom lists contain only `propext` and `Quot.sound`.

I also fixed the raw-return proof to keep the `midA2 = midApos 1` rewrite symbolic. Unfolding the variable-length zipper lists caused a local heartbeat timeout, while rewriting by the proved equality and simplifying only the parameter arithmetic compiles cleanly in a stubbed composition harness. The candidate now states:
```lean
j_high2_to_junc_raw u :
  ∃ c', run target429 (4*u*u + 44*u + 204) J(u,2*u+2) = some c' ∧
    Represents (junc 0 0 (4*u+18)) c' ∧
    c'.head = -(2*u+10)
```
This is an exact raw-source theorem conditional on the synthetic J-chart input. It does not establish blank-root reachability or decide #429.

The current candidate files are `High2Tail.lean`, `High2TailBase.lean`, and `High2Return.lean`; the manual workflow compiles all three and checks the accumulated source log for `sorryAx`. I will use one full-source acceptance run after pinning the current SHA.