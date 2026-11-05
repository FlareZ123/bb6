import FullForcedNormalize
import EvenTwo
import ReachAffine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46E2
open BB6.Agent46
open BB6.Agent3

/-- Source-certified direct affine region, with exact unique predecessor. -/
def evenTwoGate (x y : Nat) : Prop :=
  4≤y ∧ y%2=0 ∧ (x+y)%4=2

instance evenTwoGate_decidable (x y : Nat) : Decidable (evenTwoGate x y) := by
  unfold evenTwoGate
  infer_instance

/-- Normalize four independent exact original-source inverse sectors:
    odd/odd low-value, even/odd seven-sector, and two even-right affine sectors.
    Weighted mass drops by seven in the first two and four in both affine sectors. -/
def fourSectorNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    fourSectorNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    fourSectorNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    fourSectorNormalize (x+y-2) ((y-2)/2)
  else if h2 : evenTwoGate x y then
    fourSectorNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate,evenAffineGate,evenTwoGate] at *
    omega

/-- Unbounded executable exact backward reduction for all natural Machine C
    blank-section inputs. The unknown residue after normalization remains
    an open reachability question; this reduction is an iff, not a heuristic. -/
theorem blank_reach_iff_fourSectorNormalize (x y : Nat) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (fourSectorNormalize x y)) := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold fourSectorNormalize
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
            by_cases h2 : evenTwoGate x y
            · rw [dif_pos h2]
              rcases h2 with ⟨hy,heven,hs⟩
              have hh := blank_reach_iff_even_two x y hy heven hs
              have hlt : x+y-2+2*((y-2)/2)<z := by omega
              have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
              exact hh.trans hrec
            · rw [dif_neg h2]

#print axioms blank_reach_iff_fourSectorNormalize
end BB6.Agent46E2
