import CountedCarryBoundaryTraces
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42CarryLeftFrames

open BB6Coverage.Agent48Champion

/-- The exact marked-cell pattern of the 12-step A/D boundary's final
configuration: offsets 0,3,6,9,12 are one. -/
theorem ad12FinalCell_mod (i : Int) (hi : 0 ≤ i ∧ i ≤ 12) :
    (embed carryAD12Final).tape i = decide (i % 3 = 0) := by
  have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 |
      h7 | h8 | h9 | h10 | h11 | h12
  all_goals subst i <;> simp [embed, carryAD12Final]

/-- On its active frame, the A/D boundary writes exactly the every-third
pattern. This is the finite-window identity used by the long r=4k+1
left-output seed. -/
theorem ad12FinalFrameCell (bg : Int → Bool) (i : Int)
    (hi : 0 ≤ i ∧ i ≤ 12) :
    (frame carryAD12Area bg (embed carryAD12Final)).tape i =
      decide (i % 3 = 0) := by
  have ha : carryAD12Area i = true := by
    simp [carryAD12Area]
    omega
  simp [frame, ha, ad12FinalCell_mod i hi]

/-- The bridge3 final frame marks its two leftmost cells. -/
theorem bridge3FinalCell_left (i : Int)
    (hi : i = -4 ∨ i = -3) :
    (embed carryBridgeFinal3).tape i = true := by
  rcases hi with h | h
  · subst i
    simp [embed, carryBridgeFinal3]
  · subst i
    simp [embed, carryBridgeFinal3]

/-- The bridge3 frame therefore writes one at relative offsets -4 and -3. -/
theorem bridge3FinalFrameCell_left (bg : Int → Bool) (i : Int)
    (hi : i = -4 ∨ i = -3) :
    (frame carryBridgeArea3 bg (embed carryBridgeFinal3)).tape i = true := by
  have ha : carryBridgeArea3 i = true := by
    simp [carryBridgeArea3]
    rcases hi with h | h <;> omega
  simp [frame, ha, bridge3FinalCell_left i hi]

/-- Translation by a head congruent to zero converts the AD12
every-third pattern into the canonical x mod 3 = 1 output. -/
theorem ad12Offset_mod (h x : Int) (hh : h % 3 = 0) :
    (x - (h - 2)) % 3 = 0 ↔ x % 3 = 1 := by
  omega

#print axioms ad12FinalCell_mod
#print axioms ad12FinalFrameCell
#print axioms bridge3FinalCell_left
#print axioms bridge3FinalFrameCell_left
#print axioms ad12Offset_mod

end BB6Coverage.Agent42CarryLeftFrames

-- The following bridge-frame lemmas intentionally retain their historical
-- root-level names; reopen the source namespace after the first block.
open BB6Coverage.Agent48Champion

/-- The bridge0 final tape is true at offsets -1 and 0, then follows
the every-third pattern at positive offsets in its active window. -/
theorem bridge0FinalCell_pattern (i : Int) (hi : -1 ≤ i ∧ i ≤ 10) :
    (embed carryBridgeFinal0).tape i =
      (if i ≤ 0 then true else decide (i % 3 = 1)) := by
  have hc : i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨
      i = 9 ∨ i = 10 := by omega
  rcases hc with hneg | h0 | h1 | h2 | h3 | h4 | h5 |
      h6 | h7 | h8 | h9 | h10
  all_goals subst i <;> simp [embed, carryBridgeFinal0]

/-- Shifted bridge0 frame output, expressed in absolute tape coordinates.
If the old head is 0 modulo 3, the frame writes the canonical left output
pattern on its active interval. -/
theorem bridge0FrameOutput (bg : Int → Bool) (h x : Int)
    (hh : h % 3 = 0) (hi : -1 ≤ x-h ∧ x-h ≤ 10) :
    (frame (fun y => carryBridgeArea0 (y-h)) bg
      (shiftConfig h (embed carryBridgeFinal0))).tape x =
        (if x ≤ h then true else decide (x % 3 = 1)) := by
  have ha : carryBridgeArea0 (x-h) = true := by
    simp [carryBridgeArea0]
    omega
  have hf := bridge0FinalCell_pattern (x-h) hi
  have hframe :
      (frame (fun y => carryBridgeArea0 (y-h)) bg
        (shiftConfig h (embed carryBridgeFinal0))).tape x =
          (embed carryBridgeFinal0).tape (x-h) := by
    simp [frame, shiftConfig, ha]
  rw [hframe, hf]
  by_cases hx : x ≤ h
  · have hle : x-h ≤ 0 := by omega
    simp [hx, hle]
  · have hgt : ¬ x-h ≤ 0 := by omega
    have hmod : (x-h) % 3 = 1 ↔ x % 3 = 1 := by omega
    simp [hx, hgt, hmod]


/-- The bridge2 final tape is true through relative offset -2, then
has the every-third pattern with residue 2 on offsets -1..2. -/
theorem bridge2FinalCell_pattern (i : Int) (hi : -3 ≤ i ∧ i ≤ 2) :
    (embed carryBridgeFinal2).tape i =
      (if i ≤ -2 then true else decide (i % 3 = 2)) := by
  have hc : i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 := by
    omega
  rcases hc with h3 | h2 | h1 | h0 | h1p | h2p
  all_goals subst i <;> simp [embed, carryBridgeFinal2]

/-- Shifted bridge2 frame output in absolute coordinates. -/
theorem bridge2FrameOutput (bg : Int → Bool) (h x : Int)
    (hh : h % 3 = 2) (hi : -3 ≤ x-h ∧ x-h ≤ 2) :
    (frame (fun y => carryBridgeArea2 (y-h)) bg
      (shiftConfig h (embed carryBridgeFinal2))).tape x =
        (if x ≤ h-2 then true else decide (x % 3 = 1)) := by
  have ha : carryBridgeArea2 (x-h) = true := by
    simp [carryBridgeArea2]
    omega
  have hf := bridge2FinalCell_pattern (x-h) hi
  have hframe :
      (frame (fun y => carryBridgeArea2 (y-h)) bg
        (shiftConfig h (embed carryBridgeFinal2))).tape x =
          (embed carryBridgeFinal2).tape (x-h) := by
    simp [frame, shiftConfig, ha]
  rw [hframe, hf]
  by_cases hx : x ≤ h-2
  · have hle : x-h ≤ -2 := by omega
    simp [hx, hle]
  · have hgt : ¬ x-h ≤ -2 := by omega
    have hmod : (x-h) % 3 = 2 ↔ x % 3 = 1 := by omega
    simp [hx, hgt, hmod]

/-- The bridge1 final tape is true through relative offset 0, then
has the every-third pattern at offsets 1..6. -/
theorem bridge1FinalCell_pattern (i : Int) (hi : -2 ≤ i ∧ i ≤ 6) :
    (embed carryBridgeFinal1).tape i =
      (if i ≤ 0 then true else decide (i % 3 = 0)) := by
  have hc : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨
      i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases hc with h2 | h1 | h0 | h1p | h2p | h3 | h4 | h5 | h6
  all_goals subst i <;> simp [embed, carryBridgeFinal1]

/-- Shifted bridge1 frame output in absolute coordinates. -/
theorem bridge1FrameOutput (bg : Int → Bool) (h x : Int)
    (hh : h % 3 = 1) (hi : -2 ≤ x-h ∧ x-h ≤ 6) :
    (frame (fun y => carryBridgeArea1 (y-h)) bg
      (shiftConfig h (embed carryBridgeFinal1))).tape x =
        (if x ≤ h then true else decide (x % 3 = 1)) := by
  have ha : carryBridgeArea1 (x-h) = true := by
    simp [carryBridgeArea1]
    omega
  have hf := bridge1FinalCell_pattern (x-h) hi
  have hframe :
      (frame (fun y => carryBridgeArea1 (y-h)) bg
        (shiftConfig h (embed carryBridgeFinal1))).tape x =
          (embed carryBridgeFinal1).tape (x-h) := by
    simp [frame, shiftConfig, ha]
  rw [hframe, hf]
  by_cases hx : x ≤ h
  · have hle : x-h ≤ 0 := by omega
    simp [hx, hle]
  · have hgt : ¬ x-h ≤ 0 := by omega
    have hmod : (x-h) % 3 = 0 ↔ x % 3 = 1 := by omega
    simp [hx, hgt, hmod]


#print axioms bridge0FinalCell_pattern
#print axioms bridge0FrameOutput
#print axioms bridge2FinalCell_pattern
#print axioms bridge2FrameOutput
#print axioms bridge1FinalCell_pattern
#print axioms bridge1FrameOutput
