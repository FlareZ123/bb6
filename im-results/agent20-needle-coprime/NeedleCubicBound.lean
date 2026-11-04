import NeedleInverseComplete
import Lean.Elab.Tactic.Omega

namespace NeedleCubicBound
open NeedleInverse

private theorem polynomial_identity (t : Nat) :
    (2*t)*(2*t)+6*(2*t+3)=(2*t+3)*(2*t+3)+9 := by
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] <;> omega

private theorem power_den_identity (v s : Nat) :
    4*2^(2*v+s)+6*den v*2^s = den v*den v*2^s+9*2^s := by
  let t := 2^v
  have hp : (2:Nat)^(2*v+s) = (t*t)*2^s := by
    dsimp [t]
    rw [show 2*v+s=(v+v)+s by omega, Nat.pow_add, Nat.pow_add]
  have hd : den v=2*t+3 := by simp [t,den,Nat.pow_succ']
  have hsquare : 4*(t*t)=(2*t)*(2*t) := by
    change (2*2)*(t*t)=(2*t)*(2*t)
    ac_rfl
  calc
    4*2^(2*v+s)+6*den v*2^s
      = (4*(t*t)+6*(2*t+3))*2^s := by
        rw [hp,hd,Nat.add_mul]
        simp [Nat.mul_assoc]
    _ = ((2*t)*(2*t)+6*(2*t+3))*2^s := by rw [hsquare]
    _ = ((2*t+3)*(2*t+3)+9)*2^s := by rw [polynomial_identity]
    _ = den v*den v*2^s+9*2^s := by
        rw [hd]
        simp [Nat.add_mul,Nat.mul_assoc]

theorem two_v_le_pow (v : Nat) (hv : 2 ≤ v) :
    2*v ≤ (2:Nat)^v := by
  let n := v-2
  have hn : v=n+2 := by dsimp [n]; omega
  rw [hn]
  have haux : ∀ j : Nat, 2*(j+2) ≤ (2:Nat)^(j+2) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      have hj : (2:Nat)^(j+1+2)=2*2^(j+2) := by
        rw [show j+1+2=(j+2)+1 by omega, Nat.pow_succ']
      rw [hj]
      have hp : 2 ≤ (2:Nat)^(j+2) := by
        have h := Nat.pow_le_pow_right (by decide : 0 < (2:Nat))
          (show 1 ≤ j+2 by omega)
        omega
      omega
  exact haux n

theorem four_v_lt_den (v : Nat) : 4*v < den v := by
  by_cases hv : v < 2
  · have hor : v=0 ∨ v=1 := by omega
    rcases hor with h0 | h1
    · subst v; decide
    · subst v; decide
  · have hp := two_v_le_pow v (by omega)
    have hs : (2:Nat)^(v+1)=2*2^v := by rw [Nat.pow_succ']
    dsimp [den]
    rw [hs]
    omega

theorem small_power_lt_den (v s : Nat) (hs : s+3 ≤ v) :
    9*2^s+6 < den v := by
  have hpow : (2:Nat)^(s+3) ≤ 2^v :=
    Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hs
  have hscale : (2:Nat)^(s+3)=8*2^s := by
    rw [Nat.pow_add]
    change 2^s*8=8*2^s
    ac_rfl
  have hv : (2:Nat)^(v+1)=2*2^v := by rw [Nat.pow_succ']
  have hpos := Nat.one_le_two_pow (n:=s)
  dsimp [den]
  rw [hv]
  rw [hscale] at hpow
  omega

theorem terminal_modular_gate (q v s : Nat)
    (h : equation q v (2*v+s)) :
    (4*v)%(den v)=(9*2^s+6)%(den v) := by
  have heq := (equation_affine q v (2*v+s)).mp h
  have hpow := power_den_identity v s
  have hbias : 4*bias v+6=6*den v+4*v := by
    dsimp [bias,den]
    rw [Nat.pow_succ']
    omega
  have hx : 4*2^(2*v+s)+6 = den v*(4*q+6)+4*v := by
    rw [heq]
    have hm : 4*(den v*q)=den v*(4*q) := by ac_rfl
    have ha : den v*(4*q+6)=den v*(4*q)+6*den v := by
      rw [Nat.mul_add]
      rw [Nat.mul_comm (den v) 6]
    omega
  have hleft : den v*(4*q+6+6*2^s)+4*v =
      (den v*(4*q+6)+4*v)+6*den v*2^s := by
    simp [Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc,Nat.add_comm]
  have hright : den v*(den v*2^s)+(9*2^s+6) =
      den v*den v*2^s+9*2^s+6 := by
    ac_rfl
  have hbalance : den v*(4*q+6+6*2^s)+4*v =
      den v*(den v*2^s)+(9*2^s+6) := by
    rw [hleft,hright]
    omega
  have hmod := congrArg (fun n : Nat => n%den v) hbalance
  rw [Nat.mul_add_mod_self_left, Nat.mul_add_mod_self_left] at hmod
  exact hmod

theorem wedge_unique (q v s : Nat)
    (hs1 : 1 ≤ s) (hs3 : s+3 ≤ v)
    (h : equation q v (2*v+s)) :
    q=61 ∧ v=6 ∧ s=1 := by
  have hmod := terminal_modular_gate q v s h
  have hvsmall := four_v_lt_den v
  have hssmall := small_power_lt_den v s hs3
  have heq : 4*v = 9*2^s+6 := by
    rw [Nat.mod_eq_of_lt hvsmall, Nat.mod_eq_of_lt hssmall] at hmod
    exact hmod
  by_cases h1 : s=1
  · subst s
    have hv : v=6 := by omega
    subst v
    have hq : q=61 := by
      simp [equation] at h
      omega
    exact ⟨hq,rfl,rfl⟩
  · have hs2 : 2 ≤ s := by omega
    let t := s-2
    have ht : s=t+2 := by dsimp [t]; omega
    have hpow : (2:Nat)^s=4*2^t := by
      rw [ht,Nat.pow_add]
      change 2^t*4=4*2^t
      ac_rfl
    rw [hpow] at heq
    omega

/-- Every legal terminal source of valuation v requires exponent K at
least 3v-2, except the unique (K,v,q)=(13,6,61) predecessor. -/
theorem cubic_valuation_bound (q v K : Nat)
    (h : equation q v K) :
    (q=61 ∧ v=6 ∧ K=13) ∨ 3*v ≤ K+2 := by
  by_cases hc : 3*v ≤ K+2
  · exact Or.inr hc
  · have hv := NeedleValHalf.predecessor_valuation_strict q v K h
    let s := K-2*v
    have hK : K=2*v+s := by dsimp [s]; omega
    have h1 : 1 ≤ s := by dsimp [s]; omega
    have h3 : s+3 ≤ v := by dsimp [s]; omega
    have h' : equation q v (2*v+s) := by simpa only [←hK] using h
    rcases wedge_unique q v s h1 h3 h' with ⟨hq,hv',hs⟩
    left
    refine ⟨hq,hv',?_⟩
    omega

#print axioms wedge_unique
#print axioms cubic_valuation_bound
#print axioms terminal_modular_gate
#print axioms power_den_identity
end NeedleCubicBound
