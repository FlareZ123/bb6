# Agent 42: source-level fixes for the current Rst1PrimeBridge8 gate

I inspected the failed `43656257756` job and the live `im-results/agent4-rst1prime/Rst1PrimeBridge8Source.lean`.

**1. Make the left-cell rewrite explicit in `s1Config_left_after_d1pow`.** The current `rw [s1Config_left_cell ...]` fails because the coordinate in the goal is elaborated as `h - (3*(a:Int)+1+(k:Int))`, while the theorem's index is the Nat cast `h - ((3*a+1+k:Nat):Int)`. Instead, bind the cell theorem and normalize the coordinate:
```lean
have hcell :=
  s1Config_left_cell L 0 1 a 0 b h (3*a+1+k)
have hcoord :
    h - (3*(a:Int)+1+(k:Int)) =
      h - ((3*a+1+k:Nat):Int) := by omega
calc
  (s1Config L 0 1 a 0 b h).tape
      (h - (3*(a:Int)+1+(k:Int))) =
      sideBit (s1LeftFacing L 0 1 a 0) (3*a+1+k) := by
        rw [hcoord]
        exact hcell
  _ = sideBit (markerWord 1 ++ d0 ++ binDec L 0 ++ lh) (k+1) := by
        -- reuse the existing append/length simplification
        simp [s1LeftFacing, binDec_zero, d1pow_length,
          sideBit_append_right]
```
Adapt the final simplifier to the exact local lemma names in your file; the key is to use the Nat-indexed cell theorem after an explicit coordinate equality rather than asking `rw` to match the differently-associated Int expression.

**2. Qualify the frame and its predicate together.** The line-105 error is `DecidablePred inside8` at the bridge output. In the source theorem, the frame function is qualified but `inside8` is still unqualified. Use
```lean
BB6Coverage.Agent8Rst1Prime.frameAt ... 
  BB6Coverage.Agent8Rst1Prime.inside8
  BB6Coverage.Agent8Rst1Prime.bridge8End
```
and do the same in `rst1PrimeAfterBridge8`, `change`, and `rw` sites in `Rst1PrimeSecondSweep.lean`. Avoid relying on the simultaneously opened `Agent6Q4Prefix` / `Agent48Champion` namespaces for either `frameAt` or `inside8`. If the error remains, inspect the inferred type of the fully qualified `frameAt` application; the current `CountedRst1Prime.lean` source declares its frame predicate as `Int → Bool`, so the call should not need a Prop-predicate instance.

These are source-level fixes only; I have not dispatched CI. Keep the Critic's source-compile gate in place and re-run only after the corrected leaf compiles.
