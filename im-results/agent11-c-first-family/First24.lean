import ThirdStageOddDepth
import ReachAffine
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent46

/-- A new infinite first-halting-family exclusion for the authentic
    Machine C blank-origin section, using one unique affine predecessor
    and the original-source odd-special reachability barrier. -/
theorem first_halt_m24_mod32_unreachable (m k : Nat)
    (hm : m%32=24)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ (∃ time : Nat,
      BB6.Agent8Section.run secNext time (some (5,1))=some (1,k)) := by
  have hmpos : 0<m := by omega
  have hpow : 32 ∣ 2^(2*m+3) := by
    have hdiv : 2^5 ∣ 2^(2*m+3) := Nat.pow_dvd_pow 2 (by omega)
    simpa using hdiv
  have hmod : (k+3*m+4)%32=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk32 : k%32=20 := by omega
  have hkge : 4≤k := by omega
  have hkeven : k%2=0 := by omega
  have hsum : (1+k)%4=1 := by omega
  intro hreach
  obtain ⟨time,ht⟩ :=
    (BB6.Agent15.blank_reach_iff_affine 1 k hkge hkeven hsum).mp hreach
  have hfirst : 1+k-2=k-1 := by omega
  rw [hfirst] at ht
  have hfirstodd : (k-1)%2=1 := by omega
  have hsecondodd : ((k-2)/2)%2=1 := by omega
  have hmod8 : ((k-1)+(k-2)/2)%8=4 := by omega
  have hmod16 : ((k-1)+3*((k-2)/2))%16=14 := by omega
  exact BB6Agent38.blank_section_no_odd_special time (k-1) ((k-2)/2)
    hfirstodd hsecondodd hmod8 hmod16 ht

#print axioms first_halt_m24_mod32_unreachable
end BB6.Agent11
