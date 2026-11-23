import EvenOddLowStopSecondDyadic
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent13LowSecondPowerGap

private theorem linear_le_power (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

/-- Every even-index authentic low-stop unique source parent has
    a second-generation source mass S strictly between consecutive
    powers 2^(2048s+137) and 2^(2048s+138), for unbounded s.
    So S is never pure dyadic, and the a=1 exceptional original-source
    predecessor cannot appear at this second inverse level. -/
theorem second_parent_mass_strict_gap (s u : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    2^(2048*s+137) <
      173*u+25+(339*u+47)/2 ∧
    173*u+25+(339*u+47)/2 <
      2^(2048*s+138) := by
  let t := 2048*s+129
  let v := 2048*s+125
  have hlin : v+1≤2^v := linear_le_power v
  have ht : t=v+4 := by dsimp [t,v]
  have htpow : 2^t=16*2^v := by
    rw [ht,Nat.pow_add]
    simp only [show (2:Nat)^4=16 by decide]
    omega
  have hv : v=2048*s+125 := rfl
  have hsmall : 12*(685*s+49)<2^t := by
    rw [htpow]
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
  let S := 173*u+25+(339*u+47)/2
  have hEq : 2*S+12*(685*s+49)=685*2^t := by
    dsimp [S,t]
    omega
  have htpos : 0<2^t := Nat.pow_pos (by decide)
  have hlo : 512*2^t<2*S := by omega
  have hhi : 2*S<1024*2^t := by omega
  have hp8 : 2^(t+8)=256*2^t := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^8=256 by decide]
    omega
  have hp9 : 2^(t+9)=512*2^t := by
    rw [Nat.pow_add]
    simp only [show (2:Nat)^9=512 by decide]
    omega
  have hlow : 2^(t+8)<S := by rw [hp8]; omega
  have hhigh : S<2^(t+9) := by rw [hp9]; omega
  have ht8 : t+8=2048*s+137 := by dsimp [t]
  have ht9 : t+9=2048*s+138 := by dsimp [t]
  rw [ht8] at hlow
  rw [ht9] at hhigh
  exact ⟨hlow,hhigh⟩

/-- Uniform non-pure-power source mass at the second predecessor level:
    this excludes the long high-bounce a=1 exceptional inverse source
    on the *entire* even low-index family, not just finitely many s. -/
theorem second_parent_mass_not_power_two (s u : Nat)
    (hu : u+12*s+1=2^(2048*s+129)) :
    ∀ n : Nat,
       173*u+25+(339*u+47)/2 ≠ 2^n := by
  obtain ⟨hlo,hhi⟩ := second_parent_mass_strict_gap s u hu
  intro n hn
  by_cases hle : n≤2048*s+137
  · have hmon : 2^n≤2^(2048*s+137) :=
      Nat.pow_le_pow_right (by omega) hle
    omega
  · have hge : 2048*s+138≤n := by omega
    have hmon : 2^(2048*s+138)≤2^n :=
      Nat.pow_le_pow_right (by omega) hge
    omega

#print axioms second_parent_mass_strict_gap
#print axioms second_parent_mass_not_power_two
end BB6.Agent13LowSecondPowerGap
