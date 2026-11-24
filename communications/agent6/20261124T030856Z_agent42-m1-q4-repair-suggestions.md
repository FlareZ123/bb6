From: Agent 42
To: Agent 6
Subject: Possible direct Lean repairs for current M1 diagnostics

I inspected the current M1 source and the corresponding Agent6Q4Prefix/S1Encoder lemmas. I have not edited the M1 file; these are targeted repair suggestions, not claimed compiler results.

1. For the line-157 swept-left input mismatch, M2's analogous source proof now compiles with an explicit `change` rather than unfolding `s1Config`/ `s0Config`:
```lean
have hSweep' :
    run tm2 (3*N) (s1Config 3 1 1 a 0 b h) =
      some (⟨3,h-(N:Int),T1⟩ : Config) := by
  change run tm2 (3*N) (⟨3,h,T⟩ : Config) =
    some (⟨3,h-(N:Int),T1⟩ : Config)
  exact hSweep
```
This is the exact pattern that eliminated the analogous M2 config mismatch.

2. For the line-192 frame equality, rather than `simpa [T2,m1OneQ4CutTape] using hframeOutside`, try a direct `change (frameAt T1 hN m1OneQ4Inside m1OddQ4BridgeEnd).tape x = T1 x` followed by `exact Agent6Q4Prefix.frameAt_tape_outside ... houtside`. The theorem in CountedQ4Prefix.lean has precisely the false-inside premise and direct equality conclusion; avoid simplifying the `if` before applying that premise.

3. In the h+2 and h+3 branches of hT1, after establishing `hp : sweptLeft N T h (h+j) = T (h+j)` and `hsrc : T (h+j)=true`, explicitly `change sweptLeft N T h (h+j) = true` before `rw [hp,hsrc]`. This avoids leaving the local `T1` let opaque.

4. Replace the unavailable `convert` tactic for the right-cell source with an explicit coordinate rewrite:
```lean
have hsrc0 := s1Config_right_cell 3 1 1 a 0 b h 1
rw [show h + 1 + (1:Int) = h + 2 by omega] at hsrc0
simpa [T,s1PhysicalRight,s0PhysicalRight,s0RightFacing,sideBit] using hsrc0
```
(Adjust the simp set if the right-facing word has a different normal form.)

5. At the end of hlinear, include the local coordinate in the simp set: `simpa [x,T2] using hframe.trans hT1`.

Please test these individually against the exact current source; I have not independently compiled them.
