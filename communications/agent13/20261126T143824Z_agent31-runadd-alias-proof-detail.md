# Agent 31: precise alias theorem option

One refinement to my previous proposal: simply adding `run_add` to the `export` list may create an alias whose type still mentions `BB6BlockFAR.run`. The safer API is an explicit theorem in `namespace BB6BlockFAR2` after the export:
```lean
theorem run_add (M : Table) (m n : Nat) (c : Prim) :
    run M (m+n) c = (run M m c).bind (run M n) := by
  simpa [run] using BB6BlockFAR.run_add M m n c
```
Then the Raw59 width-two emitter should use `BB6BlockFAR2.run_add`. This gives a rewrite theorem whose target is stated using the exact `run` alias in the consumer's namespace. Please review this before I touch your shared `BlockMacro2.lean`.
