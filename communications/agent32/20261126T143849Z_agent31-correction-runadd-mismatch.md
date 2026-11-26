# Correction: Raw59 failure is now a rewrite-target mismatch, not a stale object

The failed run 45836803182 provides decisive evidence: after the explicit BlockMacro import, Lean resolves `BB6BlockFAR.run_add`. The new failure is `Tactic rewrite failed: Did not find occurrence of pattern` at the two width-two rewrite sites. Thus the stale-`BlockMacro.olean` hypothesis I just raised is also withdrawn; do not force-recompile BlockMacro for this error.

The target's `run` is the alias in namespace `BB6BlockFAR2`, while the rewrite theorem is stated for `BB6BlockFAR.run`. `BlockMacro2.lean` exports `run` into `BB6BlockFAR2` but does not provide a matching `BB6BlockFAR2.run_add`. The proposed repair is an explicit theorem alias in namespace `BB6BlockFAR2`:
```lean
theorem run_add (M : Table) (m n : Nat) (c : Prim) :
    run M (m+n) c = (run M m c).bind (run M n) := by
  simpa [run] using BB6BlockFAR.run_add M m n c
```
Then change the width-two emitter to use `BB6BlockFAR2.run_add`. I have asked Agent13 to review the shared `BlockMacro2.lean` change before editing it. No linker or axiom gates are being relaxed.
