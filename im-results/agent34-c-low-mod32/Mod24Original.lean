import ModImageOriginal
import ThirdStageOddDepth
import Lean.Elab.Tactic.Omega

namespace BB6Agent34
open BB6.Agent46

/-- Every authentic low halting target with m ≡ 24 (mod32) is absent
    from the complete blank-origin section orbit. The original stopping
    equation is a hypothesis, so no Nat subtraction is truncated. -/
theorem low_m24_unreachable (m k time : Nat)
    (hm : m%32=24)
    (heq : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (1,k) := by
  have hmge : 24≤m := by omega
  have hpow : 32 ∣ 2^(2*m+3) := by
    change 2^5 ∣ 2^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hmod : (k+3*m+4)%32=0 := by
    rw [heq]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hk : k%32=20 := by omega
  have hk4 : k%4=0 := by omega
  have hkmin : 4≤k := by omega
  intro hr
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
        rcases p with ⟨a,b⟩
        have ht : secNext (a,b)=some (1,k) := by
          simpa [BB6.Agent8Section.run,hp] using hr
        obtain ⟨ha,hb⟩ := one_four_target_only_direct a b k ht hkmin hk4
        have hoddA : a%2=1 := by omega
        have hoddB : b%2=1 := by omega
        have hsum : (a+b)%8=4 := by omega
        have hlinear : (a+3*b)%16=14 := by omega
        exact BB6Agent38.blank_section_no_odd_special n a b hoddA hoddB hsum hlinear hp

#print axioms low_m24_unreachable
end BB6Agent34
