import NeedleGrowth
import NeedleInverseComplete
import TwoStepParent
import Lean.Elab.Tactic.Omega

namespace BB6SpaceNeedle
open NeedleGrowth
open NeedleInverse

/-- A genuine two-edge chain in the exact Space-Needle edge law forces
    the quotient-free congruence at its second valuation. -/
theorem edge_chain_two_step_congruence
    {z b y : Nat} (h₁ : Edge b y) (h₂ : Edge z b) :
    ∃ w t : Nat, denominator t ∣ twoStepResidue w t (y : Int) := by
  rcases h₁ with ⟨q,w,hb,hy⟩
  rcases h₂ with ⟨q',t,hz,hb₂⟩
  have hfirstN : y = den w*q+bias w := by
    calc
      y = b+w+3*(q+1) := hy
      _ = 2^w*(2*q+3)+w+3*(q+1) := by rw [hb]
      _ = den w*q+bias w := affine_identity q w
  have hsecondN : b = den t*q'+bias t := by
    calc
      b = z+t+3*(q'+1) := hb₂
      _ = 2^t*(2*q'+3)+t+3*(q'+1) := by rw [hz]
      _ = den t*q'+bias t := affine_identity q' t
  have hfirstInt : (y : Int) = denominator w*(q:Int)+offset w := by
    have h := congrArg (fun n : Nat => (n : Int)) hfirstN
    simpa [denominator, offset, den, bias] using h
  have hcounterInt : firstCounter w q = (b : Int) := by
    simp [firstCounter, hb]
  have hsecondInt : firstCounter w q = denominator t*(q':Int)+offset t := by
    rw [hcounterInt]
    have h := congrArg (fun n : Nat => (n : Int)) hsecondN
    simpa [denominator, offset, den, bias] using h
  exact ⟨w,t,two_step_parent_congruence w t y q q' hfirstInt hsecondInt⟩

#print axioms edge_chain_two_step_congruence
end BB6SpaceNeedle
