import NeedleQuinticEnumerate
import Lean.Elab.Tactic.Omega
namespace NeedleQuinticRegular
open NeedleInverse

/-- Exact finite regular terminal sources, with no isolated exceptions. -/
def parents (K : Nat) : List (Nat × Nat) :=
  (List.range ((K+3)/5+1)).filterMap fun v =>
    (candidate v K).map fun q => (v,q)

/-- This exception-free list is exactly the legal affine incoming source
    set satisfying the uniform fifth-linear regular bound. -/
theorem parents_spec (q v K : Nat) :
    (v,q) ∈ parents K ↔ equation q v K ∧ 5*v≤K+3 := by
  constructor
  · intro hm
    obtain ⟨v',hr,hmap⟩ := List.mem_filterMap.mp hm
    cases hc : candidate v' K with
    | none => simp [hc] at hmap
    | some q' =>
      have hp : (v',q')=(v,q) := by simpa [hc] using hmap
      obtain ⟨hv,hq⟩ := Prod.mk.inj hp
      subst v'
      subst q'
      have hval : v ≤ (K+3)/5 := by
        have hsize := List.mem_range.mp hr
        omega
      constructor
      · exact (candidate_correct q v K).mp hc
      · have hh := (Nat.le_div_iff_mul_le (by decide : 0<(5:Nat))).mp hval
        omega
  · rintro ⟨heq,hv⟩
    apply List.mem_filterMap.mpr
    have hsize : v < (K+3)/5+1 := by
      have hh : v ≤ (K+3)/5 :=
        (Nat.le_div_iff_mul_le (by decide : 0<(5:Nat))).mpr (by omega)
      omega
    refine ⟨v,List.mem_range.mpr hsize,?_⟩
    simp [(candidate_correct q v K).mpr heq]

#print axioms parents_spec
end NeedleQuinticRegular
