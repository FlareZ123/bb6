import FullSectionInverse
import GenericSection
import Low33619
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace BB6.Agent21Low33619

/-- The independently checked abstract predecessor relation is exactly the
    original Machine C full right>=5 source inverse criterion. -/
theorem source_inverse_pred (a k x y : Nat) (hy : 5≤y)
    (h : BB6.Agent46.secNext (a,k)=some (x,y)) :
    Low33619.Pred a k x y := by
  have hp := (BB6.Agent46.complete_section_inverse a k x y hy).mp h
  change Low33619.Pred a k x y at hp
  exact hp

private theorem run_eq_source (n : Nat) (s : Option (Nat × Nat)) :
    BB6.Agent8Section.run BB6.Agent46.secNext n s =
      Low33619.runF BB6.Agent46.secNext n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (BB6.Agent8Section.run BB6.Agent46.secNext n s).bind
        BB6.Agent46.secNext =
        (Low33619.runF BB6.Agent46.secNext n s).bind BB6.Agent46.secNext
      rw [ih]

/-- Every member of the previously unresolved 30211 mod 65536 low gate ray
    is unreachable from the authentic Machine C blank section root. -/
theorem blank_no_33619_low (time u : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,65536*u+30211) := by
  rw [run_eq_source]
  exact Low33619.runF_no_33619 BB6.Agent46.secNext
    (fun a k x y hy h => source_inverse_pred a k x y hy h) time u

/-- The complete first-family stopping-index progression m=33619 modulo
    65536 is excluded, not just a finite initial segment of the true run. -/
theorem first_stop_m33619_mod65536 (time m k : Nat)
    (hm : m%65536=33619) (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,k) := by
  have hmmin : 33619≤m := by omega
  have hpow : 65536 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^16 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%65536=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%65536=30211 := by omega
  have hk : k=65536*(k/65536)+30211 := by omega
  rw [hk]
  exact blank_no_33619_low time (k/65536)

#print axioms source_inverse_pred
#print axioms blank_no_33619_low
#print axioms first_stop_m33619_mod65536
end BB6.Agent21Low33619
