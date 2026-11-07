import OddForcedNormalize
import ReachAffine
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Source-certified direct affine region, with exact unique predecessor. -/
def evenAffineGate (x y : Nat) : Prop :=
  4≤y ∧ y%2=0 ∧ (x+y)%4=1

instance evenAffineGate_decidable (x y : Nat) : Decidable (evenAffineGate x y) := by
  unfold evenAffineGate
  infer_instance

/-- Normalize four exact original-source inverse sectors:
    odd/odd 2-adic low-value, even/odd seven-sector, affine even-right,
    and the complete six-residue even-right inverse. The affine gate is
    retained for its y=4 cases; the six-residue gate extends it for y≥6.
    Weighted mass drops by seven in the first two sectors and four in both
    even-right sectors. -/
def fullForcedNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    fullForcedNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    fullForcedNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    fullForcedNormalize (x+y-2) ((y-2)/2)
  else if hs : sixEvenRightGate x y then
    fullForcedNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate,evenAffineGate,sixEvenRightGate] at *
    omega

/-- Unbounded executable exact backward reduction for all natural Machine C
    blank-section inputs. The unknown residue after normalization remains
    an open reachability question; this reduction is an iff, not a heuristic. -/
theorem blank_reach_iff_fullForcedNormalize (x y : Nat) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (fullForcedNormalize x y)) := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold fullForcedNormalize
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
            by_cases hs : sixEvenRightGate x y
            · rw [dif_pos hs]
              rcases hs with ⟨hy,heven,h0,h7⟩
              have hh := six_even_right_blank_reach_iff x y hy heven h0 h7
              have hlt : x+y-2+2*((y-2)/2)<z := by omega
              have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
              exact hh.trans hrec
            · rw [dif_neg hs]

#print axioms blank_reach_iff_fullForcedNormalize
end BB6.Agent3
