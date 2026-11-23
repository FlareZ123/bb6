import FullSectionInverse
import GenericSection
import Low56659
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace BB6.Agent21Low56659

/-- The copied predecessor predicate agrees definitionally with the authentic
    original-source full inverse criterion on all right>=5 outputs. -/
theorem source_inverse_pred (a k x y : Nat) (hy:5≤y)
    (h: BB6.Agent46.secNext (a,k) = some (x,y)) :
    Low56659.Pred a k x y := by
  have hp := (BB6.Agent46.complete_section_inverse a k x y hy).mp h
  change Low56659.Pred a k x y at hp
  exact hp

private theorem run_eq_source (n:Nat) (s:Option (Nat×Nat)) :
    BB6.Agent8Section.run BB6.Agent46.secNext n s =
      Low56659.runF BB6.Agent46.secNext n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (BB6.Agent8Section.run BB6.Agent46.secNext n s).bind
        BB6.Agent46.secNext =
        (Low56659.runF BB6.Agent46.secNext n s).bind BB6.Agent46.secNext
      rw [ih]

/-- New unbounded low-stop target ray, independent of the 33619-class. -/
theorem blank_no_56659_low (time u:Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,131072*u+92163) := by
  rw [run_eq_source]
  exact Low56659.runF_no_56659 BB6.Agent46.secNext
    (fun a k x y hy h => source_inverse_pred a k x y hy h) time u

/-- The full progression m≡56659 mod 131072 is inaccessible for the exact
    original first-family stopping equation. -/
theorem first_stop_m56659_mod131072 (time m k:Nat)
    (hm:m%131072=56659) (hstop:k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,k) := by
  have hmmin : 56659≤m := by omega
  have hpow : 131072 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^17 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%131072=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%131072=92163 := by omega
  have hk : k=131072*(k/131072)+92163 := by omega
  rw [hk]
  exact blank_no_56659_low time (k/131072)

#print axioms source_inverse_pred
#print axioms blank_no_56659_low
#print axioms first_stop_m56659_mod131072
end BB6.Agent21Low56659
