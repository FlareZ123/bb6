import NeedleQuinticRegular
import Lean.Elab.Tactic.Omega
namespace NeedleSixthRegular
open NeedleInverse

/-- Fifth-root restricted regular feeder list with a sixth-linear cutoff. -/
def parents (K : Nat) : List (Nat × Nat) :=
  (List.range ((K+4)/6+1)).filterMap fun v =>
    (candidate v K).map fun q => (v,q)

theorem parents_spec (q v K : Nat) :
    (v,q) ∈ parents K ↔ equation q v K ∧ 6*v≤K+4 := by
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
      have hval : v ≤ (K+4)/6 := by
        have hsize := List.mem_range.mp hr
        omega
      constructor
      · exact (candidate_correct q v K).mp hc
      · have hh := (Nat.le_div_iff_mul_le (by decide : 0<(6:Nat))).mp hval
        omega
  · rintro ⟨heq,hv⟩
    apply List.mem_filterMap.mpr
    have hsize : v < (K+4)/6+1 := by
      have hh : v ≤ (K+4)/6 :=
        (Nat.le_div_iff_mul_le (by decide : 0<(6:Nat))).mpr (by omega)
      omega
    refine ⟨v,List.mem_range.mpr hsize,?_⟩
    simp [(candidate_correct q v K).mpr heq]

#print axioms parents_spec
end NeedleSixthRegular
