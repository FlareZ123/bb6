import Low1875Arithmetic
import FullSectionInverse
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent21Low1875

/-- The copied arithmetic inverse predicate is definitionally the full original
    section inverse predicate on every genuine output with right counter >= 5. -/
theorem source_inverse_is_pred (a k x y : Nat) (hy : 5≤y)
    (h : BB6.Agent46.secNext (a,k)=some (x,y)) :
    Local1875.Pred a k x y := by
  have hp := (BB6.Agent46.complete_section_inverse a k x y hy).mp h
  change Local1875.Pred a k x y at hp
  exact hp

/-- The auxiliary finite-orbit interpreter agrees with the original source run. -/
theorem runF_eq_source (n : Nat) (s : Option (Nat × Nat)) :
    BB6.Agent8Section.run BB6.Agent46.secNext n s =
      Local1875.runF BB6.Agent46.secNext n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (BB6.Agent8Section.run BB6.Agent46.secNext n s).bind
        BB6.Agent46.secNext =
        (Local1875.runF BB6.Agent46.secNext n s).bind BB6.Agent46.secNext
      rw [ih]

/-- All-time exclusion from the genuine original blank section orbit. -/
theorem blank_no_1875_low (time t : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,2048*t+515) := by
  rw [runF_eq_source]
  exact Local1875.runF_no_low BB6.Agent46.secNext
    (fun a k x y hy h => source_inverse_is_pred a k x y hy h) time t

/-- No genuine first stopping gate has index 1875 modulo 2048. -/
theorem first_stop_m1875_mod2048 (time m k : Nat)
    (hm : m%2048=1875) (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,k) := by
  have hmmin : 1875≤m := by omega
  have hpow : 2048 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^11 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%2048=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%2048=515 := by omega
  have hk : k=2048*(k/2048)+515 := by omega
  rw [hk]
  exact blank_no_1875_low time (k/2048)

#print axioms source_inverse_is_pred
#print axioms runF_eq_source
#print axioms blank_no_1875_low
#print axioms first_stop_m1875_mod2048
end BB6.Agent21Low1875
