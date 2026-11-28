import Lean
import Lean.Elab.Tactic.Omega

namespace NeedleRotation.Asymmetric

/-- Every forbidden residue has exactly one shift modulo m. -/
def badShifts (m e B : Nat) : List Nat :=
  (List.range B).map fun j => (m-B+j+(m-e%m))%m

theorem badShifts_length (m e B : Nat) : (badShifts m e B).length = B := by
  simp [badShifts]

theorem badShift_mem (m e B h : Nat) (hm : 0<m) (hh : h<m)
    (hB : B≤m) (hb : m-B ≤ (e+h)%m) : h ∈ badShifts m e B := by
  let j := (e+h)%m-(m-B)
  have ht := Nat.mod_lt (e+h) hm
  have hj : j<B := by dsimp [j]; omega
  have hres : m-B+j=(e+h)%m := by dsimp [j]; omega
  apply List.mem_map.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  rw [hres, Nat.mod_add_mod]
  have he : (e+(m-e%m))%m=0 := by
    rw [←Nat.mod_add_mod]
    have heq : e%m+(m-e%m)=m := by have := Nat.mod_lt e hm; omega
    rw [heq,Nat.mod_self]
  rw [show e+h+(m-e%m)=e+(m-e%m)+h by omega,←Nat.mod_add_mod,he,Nat.zero_add,Nat.mod_eq_of_lt hh]

/-- Unequal forbidden widths pay their sum, rather than 3 times their maximum. -/
theorem exists_weighted_shift (m e f B₁ B₂ B₃ : Nat)
    (hsize : B₁+B₂+B₃<m) :
    ∃ h<m, (e+h)%m+B₁<m ∧ (f+h)%m+B₂<m ∧ h+B₃<m := by
  have hm : 0<m := by omega
  let bad := badShifts m e B₁ ++ badShifts m f B₂ ++ badShifts m 0 B₃
  have hlen : bad.length = B₁+B₂+B₃ := by simp [bad,badShifts_length,Nat.add_assoc]
  have hex : ∃ h<m, h ∉ bad := by
    by_cases h : ∃ h<m, h ∉ bad
    · exact h
    · exfalso
      have hsub : List.range m ⊆ bad := by
        intro j hj
        by_cases hmemb : j ∈ bad
        · exact hmemb
        · exact False.elim (h ⟨j,List.mem_range.mp hj,hmemb⟩)
      have hle := List.nodup_range.length_le_of_subset hsub
      simp [hlen] at hle
      omega
  obtain ⟨h,hh,hn⟩ := hex
  refine ⟨h,hh,?_,?_,?_⟩
  · by_cases hb : (e+h)%m+B₁<m
    · exact hb
    · have hx := badShift_mem m e B₁ h hm hh (by omega) (by omega)
      exact False.elim (hn (by simp [bad,hx]))
  · by_cases hb : (f+h)%m+B₂<m
    · exact hb
    · have hx := badShift_mem m f B₂ h hm hh (by omega) (by omega)
      exact False.elim (hn (by simp [bad,hx]))
  · by_cases hb : h+B₃<m
    · exact hb
    · have hx := badShift_mem m 0 B₃ h hm hh (by omega) (by simp [Nat.mod_eq_of_lt hh]; omega)
      exact False.elim (hn (by simp [bad,hx]))

#print axioms exists_weighted_shift
end NeedleRotation.Asymmetric
