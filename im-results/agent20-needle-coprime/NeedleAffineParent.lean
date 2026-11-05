import Lean.Elab.Tactic.Omega
namespace NeedleAffineParent

theorem affine_parent (d r x : Nat)
    (hd : 0<d) (hx : d+r ≤ x) (hmod : x%d=r) :
    ∃ q : Nat, d*q+(d+r)=x := by
  have hQ : 1 ≤ x/d := by
    by_cases hzero : x/d=0
    · have hdiv := Nat.mod_add_div x d
      simp [hzero,hmod] at hdiv
      omega
    · exact Nat.one_le_iff_ne_zero.mpr hzero
  refine ⟨x/d-1, ?_⟩
  have hsub : x/d-1+1=x/d := Nat.sub_add_cancel hQ
  have hadd : d*(x/d-1)+d=d*(x/d) := by
    calc
      d*(x/d-1)+d = d*((x/d-1)+1) := by rw [Nat.mul_add]; omega
      _ = d*(x/d) := by rw [hsub]
  have hdiv := Nat.mod_add_div x d
  omega

#print axioms affine_parent
end NeedleAffineParent
