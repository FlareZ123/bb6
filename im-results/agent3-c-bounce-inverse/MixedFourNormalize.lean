import FullForcedNormalize
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Fully mixed exact predecessor normalization of four source-certified
    inverse regions. Each selected edge decreases weighted mass. -/
def mixedFourNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    mixedFourNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    mixedFourNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    mixedFourNormalize (x+y-2) ((y-2)/2)
  else if hs : BB6.Agent46.sixEvenRightGate x y then
    mixedFourNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate, evenSevenGate, evenAffineGate,
      BB6.Agent46.sixEvenRightGate] at *
    omega

/-- Every normalization step is an exact original-source reachability iff,
    for the actual (5,1) blank section entry at all times. -/
theorem mixedFourNormalize_reach_iff (x y : Nat) :
    CReach x y ↔ CReach (mixedFourNormalize x y).1 (mixedFourNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold mixedFourNormalize
      by_cases hg : oddLowGate x y
      · rw [dif_pos hg]
        rcases hg with ⟨hx,hy,hy5,h4,h16,hsize⟩
        have hh := oddodd_lowval_blank_reach_iff x y hx hy hy5 h4 h16 hsize
        have hlt : ((x+y-4)/2)+2*((x+3*y-10)/4)<z := by omega
        have hrec := ih _ hlt ((x+y-4)/2) ((x+3*y-10)/4) (by rfl)
        exact hh.trans hrec
      · rw [dif_neg hg]
        by_cases he : evenSevenGate x y
        · rw [dif_pos he]
          rcases he with ⟨hx,hy,hy5,hseven,hsize⟩
          have hh := odd_seven_blank_reach_iff x y hx hy hy5 hseven hsize
          have hlt : ((x+y-5)/2)+2*((x+3*y-9)/4)<z := by omega
          have hrec := ih _ hlt ((x+y-5)/2) ((x+3*y-9)/4) (by rfl)
          exact hh.trans hrec
        · rw [dif_neg he]
          by_cases hf : evenAffineGate x y
          · rw [dif_pos hf]
            rcases hf with ⟨hy,heven,hs⟩
            have hh := BB6.Agent15.blank_reach_iff_affine x y hy heven hs
            have hlt : x+y-2+2*((y-2)/2)<z := by omega
            have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
            exact hh.trans hrec
          · rw [dif_neg hf]
            by_cases hs : BB6.Agent46.sixEvenRightGate x y
            · rw [dif_pos hs]
              rcases hs with ⟨hy,heven,h0,h7⟩
              have hh := BB6.Agent46.six_even_right_blank_reach_iff x y hy heven h0 h7
              have hlt : x+y-2+2*((y-2)/2)<z := by omega
              have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
              exact hh.trans hrec
            · rw [dif_neg hs]

#print axioms mixedFourNormalize_reach_iff
end BB6.Agent3
