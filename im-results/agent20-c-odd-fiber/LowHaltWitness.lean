import OddFan
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20OddFan
open BB6.Agent46 BB6.Agent3 BB6.Agent15

/-- Every low parametric gate is an authentic terminating section input,
    by the original-source closed halting criterion. -/
theorem low_gate_halts (m : Nat) :
    secNext (1,2^(2*m+3)-3*m-4)=none := by
  have h4 := parent_four_ge m
  have hpow : 2^(2*m+3)=8*4^m := by
    rw [Nat.pow_add 2 (2*m) 3,degree_two_pow_double]
    omega
  have hm := Nat.mul_le_mul_left 8 h4
  have hbound : 3*m+4≤2^(2*m+3) := by omega
  have hk : (2^(2*m+3)-3*m-4)+3*m+4=2^(2*m+3) := by omega
  apply (section_halts_iff_parametric 1 (2^(2*m+3)-3*m-4)).mpr
  exact Or.inr (Or.inl ⟨rfl,m,hk⟩)

/-- Complete finite fiber of terminating inputs m+1=4^t.
    There are exactly t original section edges into such a halting input. -/
theorem low_four_power_halt_fiber (m t : Nat) (ht : 1≤t)
    (hm : m+1=4^t) :
    secNext (1,2^(2*m+3)-3*m-4)=none ∧
    ∃ C : Nat, 5≤C ∧ C%2=1 ∧
      ((∀ r : Fin t,
        secNext (oddSource t C r)=some (1,2^(2*m+3)-3*m-4)) ∧
       Function.Injective (oddSource t C) ∧
       (∀ a k, secNext (a,k)=some (1,2^(2*m+3)-3*m-4) →
         ∃ r : Fin t, oddSource t C r=(a,k))) := by
  exact ⟨low_gate_halts m,low_gate_exact_fiber m t ht hm⟩

#print axioms low_four_power_halt_fiber
end BB6.Agent20OddFan
