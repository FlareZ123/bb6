import Std

/-!
Standalone Lean 4.36.0-rc2 certificate for the 5-adic exponent family used
in Agent 40's bounded-history Sheep proof-method obstruction.

Proves:
  5^(k+1) divides 4^(5^k)+1;
  5^(k+1) divides 2^(2*5^k+1)+2.

No imported original Turing-machine semantics or all-time Sheep decision.
Proof relies only on Lean's Std/Init theorems and the kernel checked grind.
-/

namespace SheepPowerAncestors

private theorem five_lift (k : Nat) (t : Int)
    (h : (5 : Int)^(k+1) ∣ t+1) :
    (5 : Int)^(k+2) ∣ t^5+1 := by
  have h5pow : (5 : Int) ∣ (5 : Int)^(k+1) := by
    refine ⟨(5:Int)^k, ?_⟩
    rw [Int.pow_add]
    grind
  have h5 : (5 : Int) ∣ t+1 := Int.dvd_trans h5pow h
  have hfactor : t^5+1 = (t+1)*(5+(t+1)*(t^3-2*t^2+3*t-4)) := by
    grind
  have hf : (5 : Int) ∣ 5+(t+1)*(t^3-2*t^2+3*t-4) := by
    exact Int.dvd_add (Int.dvd_refl _) (Int.dvd_mul_of_dvd_left h5)
  rcases h with ⟨u, hu⟩
  rcases hf with ⟨v, hv⟩
  have hexp : (5:Int)^(k+2) = (5:Int)^(k+1)*5 := by
    have hh : k+2 = (k+1)+1 := by omega
    rw [hh,Int.pow_add]
    grind
  refine ⟨u*v, ?_⟩
  rw [hfactor,hv,hu,hexp]
  grind

theorem power_divisibility (k : Nat) :
    (5 : Int)^(k+1) ∣ (4 : Int)^(5^k)+1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := five_lift k ((4:Int)^(5^k)) ih
    have hp : (4:Int)^(5^(k+1)) = ((4:Int)^(5^k))^5 := by
      rw [Nat.pow_succ,Int.pow_mul]
    rw [hp]
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using h

#print axioms power_divisibility

theorem power_two_target (k : Nat) :
    (5:Int)^(k+1) ∣ (2:Int)^(2*5^k+1)+2 := by
  have h := power_divisibility k
  have heq : (2:Int)^(2*5^k+1)+2 = 2*((4:Int)^(5^k)+1) := by
    rw [Int.pow_add,Int.pow_mul]
    grind
  rw [heq]
  exact Int.dvd_mul_of_dvd_right h

#print axioms power_two_target
end SheepPowerAncestors
