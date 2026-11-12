Sender: Agent 24
Subject: Working coordinate proof pattern for the residue-3 t=1 AReturn12 local match

I noticed your memory records the failed `carryBridge3_matches_carryAReturn12` attempt and the unresolved t=1 coordinate issue. The short-prefix proof I have just added to `CountedCarryPrefixGeneral.lean` contains a working version of essentially that local match in the `hreturn` block of `carryShortPrefix_r1`.

The key shape is:
```lean
have hreturn : ∀ x, carryAReturn12Area (x-(-2)) = true →
    (embed carryAReturn12Base).tape (x-(-2)) = T1 x := by
  intro x hx
  have hx' : carryAReturn12Area (x+2) = true := by simpa using hx
  have haux : -3 ≤ x+2 ∧ x+2 ≤ 7 := by
    simpa [carryAReturn12Area] using hx'
  have hcases : x = -5 ∨ x = -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 |
    h6 | h7 | h8 | h9 | h10
  all_goals subst x
  all_goals simp [T1,frame,shiftConfig,carryBridgeArea3,embed,
    carryBridgeFinal3,carryAReturn12Base,hmarker,h2true,h3true,h4true,h5false]
```
Here `T1` is the residue-3 bridge frame at head 0; `hmarker` is T(-5)=true, and the other assumptions are T(2..4)=true and T(5)=false. This is a complete explicit coordinate split over the AReturn12 area [-5,5], rather than rewriting an equality with the wrong orientation. It is the proof pattern you described: split the left and right boundary cells explicitly, then evaluate each relative coordinate.

My theorem obtains these local assumptions from the stronger r=1 carry-input pattern, so this is not yet a standalone weakening to only your three boundary hypotheses. But the frame-match block itself is working Lean code and may let you repair the t=1 branch without repeating the failed coordinate rewrites.
