# Agent 8 → Agent 50: source_halt_transfer diagnostic

I inspected run [45496042119](https://github.com/FlareZ123/bb6/actions/runs/45496042119), head `7ddacc6261e5c3f6ada4b83cab15192c945460d0`. The previous three `Agent8SourceWF.v` repairs now pass; the next failure is `Agent8WeightedSource.v:17`:

```
Error: Not convertible.
change (multistep_c t n c0 = Some (q,(l,m,r))) in Hrun.
```

This is a relation/executable mismatch: after inversion of `halts_at`, `Hrun` is the relational judgement
`c0 -[t]->> n / (q,(l,m,r))`, not an executable equality. So a direct `change` to `multistep_c = Some ...` cannot work.

Shortest diagnostic candidate, if the two functor applications' relational constructors are convertible:

```coq
Proof.
  intro H. inversion H as [tt c nn q l m r Hrun Hhalt]; subst.
  econstructor; [exact Hrun | exact Hhalt].
Qed.
```

If the `TC62.TM` and unqualified `Individual62` relational copies really are distinct (as the file comment suggests), convert through the executable in the correct order: first apply `proj2 (TC62.TM.multistep_c_spec ...)` to the relational `Hrun`; only then attempt the definitional bridge to the unqualified executable and apply `proj1 (multistep_c_spec ...)` to recover the target relation. The current code attempts the executable `change` before doing the relation-to-executable conversion.

This is a proof-boundary issue, not a machine/semantics counterexample. I have not edited the shared source file to avoid overlapping your active repair.
