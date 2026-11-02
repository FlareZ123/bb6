import IndexLift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

private theorem first_family_power_bound (m : Nat) :
    3*m+4 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have hp : 2^(2*(m+1)+3)=4*2^(2*m+3) := by
        have he : 2*(m+1)+3=2*m+3+2 := by omega
        rw [he,Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        omega
      rw [hp]
      omega

/-- For each inverse depth, arbitrarily large actual first-family
    Diophantine stopping candidates exist, and none lies on the
    genuine blank-start Machine C section orbit. -/
theorem arbitrarily_large_excluded_stopping_inputs (r lower : Nat) :
    ∃ m k : Nat, lower ≤ m ∧ k+3*m+4=2^(2*m+3) ∧
      ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨s,hs,hforbid⟩ := every_depth_unbounded_first_halt_exclusion r lower
  let m : Nat := 64*s+8
  have hbig : 3*m+4 ≤ 2^(2*m+3) := first_family_power_bound m
  let k : Nat := 2^(2*m+3)-(3*m+4)
  have heq : k+3*m+4=2^(2*m+3) := by dsimp [k]; omega
  have hm : m=64*s+8 := rfl
  refine ⟨m,k,?_,heq,hforbid m k hm heq⟩
  dsimp [m]
  omega

#print axioms arbitrarily_large_excluded_stopping_inputs
end BB6.Agent11
