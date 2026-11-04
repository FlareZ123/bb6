import FullForcedNormalize
import EvenEvenReach
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent3 BB6.Agent46

/-- Fourth exact Machine C inverse sector, disjoint from the old O/E/A gates. -/
def evenEvenGate (x y : Nat) : Prop :=
  x%2=0 ∧ y%2=0 ∧ 6≤y ∧ (x+y)%8≠0

instance evenEvenGate_decidable (x y : Nat) : Decidable (evenEvenGate x y) := by
  unfold evenEvenGate
  infer_instance

/-- A terminating exact backward normalizer containing O, E, A and B. -/
def fourForcedNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    fourForcedNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    fourForcedNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else if hf : evenAffineGate x y then
    fourForcedNormalize (x+y-2) ((y-2)/2)
  else if hb : evenEvenGate x y then
    fourForcedNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate,evenAffineGate,evenEvenGate] at *
    omega

/-- Every reduction is a real, uniquely reversible section edge.
    Thus normalization preserves genuine blank-origin reachability. -/
theorem blank_reach_iff_fourForcedNormalize (x y : Nat) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (fourForcedNormalize x y)) := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold fourForcedNormalize
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
            have hh := blank_reach_iff_affine x y hy heven hs
            have hlt : x+y-2+2*((y-2)/2)<z := by omega
            have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
            exact hh.trans hrec
          · rw [dif_neg hf]
            by_cases hb : evenEvenGate x y
            · rw [dif_pos hb]
              rcases hb with ⟨hx,hy,hy6,hs⟩
              have hh := blank_reach_iff_even_even x y hx hy hy6 hs
              have hlt : x+y-2+2*((y-2)/2)<z := by omega
              have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
              exact hh.trans hrec
            · rw [dif_neg hb]

#print axioms blank_reach_iff_fourForcedNormalize
end BB6.Agent15
