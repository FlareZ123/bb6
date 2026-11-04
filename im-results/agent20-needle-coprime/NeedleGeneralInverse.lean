import NeedleInverseComplete
import Lean.Elab.Tactic.Omega

namespace NeedleGeneralInverse
open NeedleInverse

def quotientCandidate (v y : Nat) : Nat := (y-bias v)/den v

def candidate (v y : Nat) : Option Nat :=
  if den v*quotientCandidate v y+bias v=y then
    some (quotientCandidate v y)
  else none

theorem quotient_correct (q v y : Nat) (h : y=den v*q+bias v) :
    quotientCandidate v y = q := by
  have hm : y-bias v=den v*q := by omega
  simp only [quotientCandidate, hm]
  exact Nat.mul_div_cancel_left q (by simp [den] : 0<den v)

theorem candidate_spec (q v y : Nat) :
    candidate v y=some q ↔ y=den v*q+bias v := by
  constructor
  · intro hc
    unfold candidate at hc
    split at hc
    · case isTrue he =>
      have hq : quotientCandidate v y=q := by simpa using hc
      simpa [hq] using he.symm
    · contradiction
  · intro he
    have hc : quotientCandidate v y=q := quotient_correct q v y he
    simp only [candidate, hc, show den v*q+bias v=y from he.symm, ite_true]

theorem v_upper (v q y : Nat) (he : y=den v*q+bias v) :
    v ≤ Nat.log2 y := by
  have hp : (2:Nat)^v ≤ y := by
    rw [he]
    simp only [den,bias]
    have hz : 0 ≤ (2^(v+1)+3)*q := Nat.zero_le _
    omega
  have hy : y ≠ 0 := by
    have hp' : 0 < (2:Nat)^v := Nat.pow_pos (by decide)
    omega
  by_cases hsmall : v ≤ y.log2
  · exact hsmall
  · have hlt : y.log2 < v := by omega
    have hylt : y < (2:Nat)^v := (Nat.log2_lt hy).mp hlt
    omega

theorem parent_successor_iff (d e q v : Nat)
    (hd : d+2=2^v*(2*q+3)) :
    e+2=den v*q+bias v ↔ e=d+v+3*(q+1) := by
  rw [←affine_identity q v]
  omega

def parents (y : Nat) : List (Nat × Nat) :=
  (List.range (y.log2+1)).filterMap fun v =>
    (candidate v y).map fun q => (v,q)

theorem parents_spec (q v y : Nat) :
    (v,q) ∈ parents y ↔ y=den v*q+bias v := by
  constructor
  · intro h
    obtain ⟨v',hsize,hmap⟩ := List.mem_filterMap.mp h
    cases hc : candidate v' y with
    | none => simp [hc] at hmap
    | some q' =>
      have hp : (v',q')=(v,q) := by simpa [hc] using hmap
      obtain ⟨hv,hq⟩ := Prod.mk.inj hp
      subst v'
      subst q'
      exact (candidate_spec q v y).mp hc
  · intro he
    apply List.mem_filterMap.mpr
    refine ⟨v, List.mem_range.mpr ?_, ?_⟩
    · have hv := v_upper v q y he
      omega
    · simp [(candidate_spec q v y).mpr he]

theorem fanin_bound (y : Nat) : (parents y).length ≤ y.log2+1 := by
  simpa only [parents, List.length_range] using
    (List.length_filterMap_le
      (fun v => (candidate v y).map fun q => (v,q)) (List.range (y.log2+1)))

#eval parents 16
#eval parents 256
#eval parents 8192
#print axioms parent_successor_iff
#print axioms parents_spec
#print axioms fanin_bound
end NeedleGeneralInverse
