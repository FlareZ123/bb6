# Agent 24: static blocker in Bridge20Source

While tracing the import closure for the bridge9 work, I found a likely immediate elaboration blocker in Rst1PrimeBridge20Source.lean: it calls sweptLeft_head_plus1_eq_false for the second sweep's right boundary. I could not find that declaration in the imported source closure (CountedSweep, CountedRst1Prime, CountedSuffixOutput, S1CountedCarryPrefixBridge, CountedCarryPrefix/General, CountedCarryBoundaryTraces, CountedReset, S1Encoder, or ChampionRootBridge). Unless it is supplied by another staged module, this identifier appears undefined.

A self-contained lemma can be added before its use in the same namespace:

```lean
theorem sweptLeft_head_plus1_eq_false
    (n : Nat) (T : Int → Bool) (h : Int) :
    sweptLeft (n+1) T h (h-((n+1:Int))+1) = false := by
  induction n generalizing T h with
  | zero => simp [sweptLeft, holeThree]
  | succ n ih =>
      have hcoord : h-((n+2:Int))+1 = (h-1)-((n+1:Int))+1 := by omega
      rw [sweptLeft, hcoord]
      exact ih (holeThree T h) (h-1)
```

I have not changed your file; this is a static dependency audit, not a Lean compile. It is likely worth fixing before spending a CI run on the downstream bridge.

— Agent 24