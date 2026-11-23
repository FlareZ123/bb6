import EvenOddLowStopDivisor
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowSecondDyadic

private theorem linear_le_power (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- A SECOND-GENERATION all-exponent 2-adic inverse identity for the
    genuine unique parent of every even-index low-stop target.

    Given u+12s+1=2^(2048s+129), write
    P=(173u+24,(339u+47)/2). The next backwards branching mass is
    S=(173u+24)+(339u+47)/2+1.

    For ALL n, its exact 2-divisibility is governed by the much
    smaller linear index 3*(685s+49):
       2^(n+2) | (2*S)  iff  2^n | 3*(685s+49).
    This captures the complete high-valuation spectrum at a second
    original-source inverse level, without a finite cutoff. -/
theorem second_low_parent_mass_dyadic_iff
    (s u n : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    (2^(n+2) ∣ 2*(173*u+25+(339*u+47)/2)) ↔
    (2^n ∣ 3*(685*s+49)) := by
  let t := 2048*s+129
  let v := 2048*s+125
  have hlin : v+1≤2^v := linear_le_power v
  have ht : t=v+4 := by dsimp [t,v]; omega
  have htpow : 2^t=16*2^v := by
    rw [ht,Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  have hsmall : 4*(3*(685*s+49)) < 2^t := by
    dsimp [v] at hlin
    omega
  have hpow2 : 2∣(2:Nat)^t := by
    have hd : (2:Nat)^1∣2^t :=
      Nat.pow_dvd_pow 2 (by dsimp [t]; omega)
    simpa only [show (2:Nat)^1=2 by decide] using hd
  have hmod : (2^t)%2=0 := Nat.mod_eq_zero_of_dvd hpow2
  have huodd : u%2=1 := by dsimp [t] at hmod; omega
  have hkm : (339*u+47)%2=0 := by omega
  have hktwice : 2*((339*u+47)/2)=339*u+47 := by
    have hh := Nat.mod_add_div (339*u+47) 2
    omega
  have heq :
      2*(173*u+25+(339*u+47)/2)+4*(3*(685*s+49))=
        685*2^t := by
    dsimp [t]
    omega
  exact BB6.Agent13LowFanDivisor.subtract_small_power_divisor_iff
    t n 685
    (2*(173*u+25+(339*u+47)/2))
    (3*(685*s+49))
    (by omega) hsmall heq

#print axioms second_low_parent_mass_dyadic_iff
end BB6.Agent13LowSecondDyadic
