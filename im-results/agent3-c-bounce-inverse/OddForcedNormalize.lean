import OddSevenOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Large odd/odd section returns with exact 2-adic total valuation 2 or 3. -/
def oddLowGate (x y : Nat) : Prop :=
  x%2=1 ∧ y%2=1 ∧ 5≤y ∧ (x+y)%4=0 ∧ (x+y)%16≠0 ∧ 24≤x+y

/-- Large even/odd returns at exact valuation 3 of total mass plus one. -/
def evenSevenGate (x y : Nat) : Prop :=
  x%2=0 ∧ y%2=1 ∧ 5≤y ∧ (x+y+1)%16=8 ∧ 23≤x+y

instance oddLowGate_decidable (x y : Nat) : Decidable (oddLowGate x y) := by
  unfold oddLowGate
  infer_instance

instance evenSevenGate_decidable (x y : Nat) : Decidable (evenSevenGate x y) := by
  unfold evenSevenGate
  infer_instance

/-- Automatically strip all forced inverse edges from the two source-exact
    regions. Every applied edge decreases weighted mass by exactly seven,
    hence termination holds without fuel, cutoffs, or unproved orbit claims. -/
def oddForcedNormalize (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    oddForcedNormalize ((x+y-4)/2) ((x+3*y-10)/4)
  else if he : evenSevenGate x y then
    oddForcedNormalize ((x+y-5)/2) ((x+3*y-9)/4)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate] at *
    omega

/-- Fully unbounded exact source reachability invariant under recursive
    backward normalization. This is an executable partial decision reduction,
    even for astronomically large natural counter values. -/
theorem blank_reach_iff_oddForcedNormalize (x y : Nat) :
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run secNext n (some (5,1))=
      some (oddForcedNormalize x y)) := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold oddForcedNormalize
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

#print axioms blank_reach_iff_oddForcedNormalize
end BB6.Agent3
