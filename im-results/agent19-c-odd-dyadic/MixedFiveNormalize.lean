import MixedFourNormalize
import OddSevenForcedRoot
import MixedFastRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Five
open BB6.Agent3 BB6.Agent46

def sevenGate (x y : Nat) : Prop :=
  x%2=1 ∧ y%8=6 ∧ (x+y+1)%32=16 ∧ 48≤x+y+1

instance sevenGate_decidable (x y : Nat) : Decidable (sevenGate x y) := by
  unfold sevenGate
  infer_instance

/-- Fully mixed exact predecessor normalization of four source-certified
    inverse regions. Each selected edge decreases weighted mass. -/
def mixedFiveNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    mixedFiveNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    mixedFiveNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    mixedFiveNormalize (x+y-2) ((y-2)/2)
  else if hs : BB6.Agent46.sixEvenRightGate x y then
    mixedFiveNormalize (x+y-2) ((y-2)/2)
  else if hn : sevenGate x y then
    mixedFiveNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate, evenSevenGate, evenAffineGate,
      BB6.Agent46.sixEvenRightGate, sevenGate] at *
    omega

/-- Every normalization step is an exact original-source reachability iff,
    for the actual (5,1) blank section entry at all times. -/
theorem mixedFiveNormalize_reach_iff (x y : Nat) :
    CReach x y ↔ CReach (mixedFiveNormalize x y).1 (mixedFiveNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold mixedFiveNormalize
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
              by_cases hn : sevenGate x y
              · rw [dif_pos hn]
                rcases hn with ⟨hx,hy,hmod,hbig⟩
                have hh := BB6.Agent19Seven.sumseven_forced_root_iff
                  x y hx hy hmod hbig
                have hlt : x+y-2+2*((y-2)/2)<z := by omega
                have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
                exact hh.trans hrec
              · rw [dif_neg hn]

/-- Exact fixed-target blank-root decision after five source-certified
    original-blank predecessor normalizations. -/
def mixedFiveFastRootDecision (x y : Nat) : Bool :=
  let p := mixedFiveNormalize x y
  BB6.Agent11Fast.backwardFastFuel ((p.1+2*p.2)/2) p

theorem mixedFiveFastRootDecision_iff (x y : Nat) :
    mixedFiveFastRootDecision x y=true ↔ CReach x y := by
  unfold mixedFiveFastRootDecision
  have hh := BB6.Agent11Fast.backwardFastFuelHalfFull_iff
    (mixedFiveNormalize x y).1 (mixedFiveNormalize x y).2
  change _ ↔ CReach (mixedFiveNormalize x y).1
                        (mixedFiveNormalize x y).2 at hh
  exact hh.trans (mixedFiveNormalize_reach_iff x y).symm

#print axioms mixedFiveNormalize_reach_iff
#print axioms mixedFiveFastRootDecision_iff
end BB6.Agent19Five
