import M8GenericLegacyPass
import ModularConeBlindHigh
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent15Research
open BB6.Agent29Depth
open BB6.Agent42ModularCone

/-- Every sufficiently deep member of the generic M8 Diophantine cylinder
    is invisible to Agent42's adaptive modular high-stop exclusion. -/
theorem generic_deep_modular_cone_blind
    (m d t j : Nat)
    (hm : m%2=1)
    (hd : 2*m+2≤d)
    (heq : allOddQ m*(j+3)=m+2^d*(2+8*t)) :
    highStopExcluded (j+1) m = false := by
  have hdivB := generic_high_index_multiple m d t j hd heq
  have hdiv : 2^(2*m+2) ∣ j+3*m+3 := by
    simpa [allOddB] using hdivB
  have htwo : 2 ∣ 2^(2*m+2) := by
    obtain ⟨e,he⟩ : ∃e,2*m+2=1+e := ⟨2*m+1,by omega⟩
    refine ⟨2^e,?_⟩
    rw [he,Nat.pow_add]
  have hsum2 : (j+3*m+3)%2=0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans htwo hdiv)
  have hj2 : j%2=0 := by omega
  have hpowle : 2^(2*m+2)≤2^d :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hd
  have hfactor : 2≤2+8*t := by omega
  have hlarge : 2*allOddB m≤2^d*(2+8*t) := by
    have h := Nat.mul_le_mul hpowle hfactor
    simpa [allOddB,Nat.mul_comm] using h
  have hBeq := allOdd_BQ m
  have hjpos : 1≤j := by
    by_cases hj0 : j=0
    · rw [hj0] at heq
      simp only [Nat.zero_add] at heq
      rw [hBeq] at hlarge
      omega
    · exact Nat.one_le_iff_ne_zero.mpr hj0
  exact high_stop_blind_of_even_divisible j m hjpos hj2 hm hdiv

/-- Strictness on the full deep generic M8 class: the modular checker accepts
    each parameter as unresolved while the source quotient theorem proves the
    corresponding exact Machine-C target unreachable. -/
theorem generic_deep_strict_beyond_modular_cone
    (m d t j : Nat)
    (hm : m%2=1)
    (hd : 2*m+2≤d)
    (hdpar : 2*d%4=(m+1)%4)
    (heq : allOddQ m*(j+3)=m+2^d*(2+8*t)) :
    highStopExcluded (j+1) m = false ∧
    ¬ BB6.Agent15.CReach (2*j+3) (3*2^d*(2+8*t)-2) :=
  ⟨generic_deep_modular_cone_blind m d t j hm hd heq,
   high_m8_diophantine_exclusion m d t j hm (by omega) hdpar heq⟩

#print axioms generic_deep_modular_cone_blind
#print axioms generic_deep_strict_beyond_modular_cone
end BB6.Agent15Research
