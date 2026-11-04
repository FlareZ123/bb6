import NeedleTwoStepOdd
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.NeedleTwoStepOdd

/-- A certified power-of-two period determines all other exponents
modulo an arbitrary positive modulus. -/
theorem pow_period_reduce (m period k : Nat)
    (hm : 0<m) (hp : 0<period) (hper : (2:Nat)^period%m=1) :
    (2:Nat)^k%m=2^(k%period)%m := by
  let q := k/period
  have heq : k=period*q+k%period := by
    dsimp [q]
    have hx := Nat.mod_add_div k period
    omega
  have hm2 : 1<m := by
    have hx := Nat.mod_lt ((2:Nat)^period) hm
    omega
  have hq : ∀ z : Nat, ((2:Nat)^period)^z % m=1 := by
    intro z
    induction z with
    | zero =>
      exact Nat.mod_eq_of_lt hm2
    | succ z ih =>
      rw [Nat.pow_succ',Nat.mul_mod,ih,hper]
      exact Nat.mod_eq_of_lt hm2
  rw [heq,Nat.pow_add,Nat.mul_mod]
  have hpow : (2:Nat)^(period*q)=((2:Nat)^period)^q := by rw [Nat.pow_mul]
  rw [hpow,hq]
  simp

/-- Finite residue certificates (a period and a checked finite set) exclude
whole infinite parameter fibers from the odd-terminal predecessor equation. -/
theorem period_sieve_excludes (v period : Nat)
    (hp : 0<period) (hper : (2:Nat)^period % modulus v = 1)
    (hmiss : ∀ r : Fin period, 2^r.val%modulus v ≠ offset v%modulus v)
    (q K : Nat) : ¬2^(K+1)=modulus v*q+offset v := by
  have hM : 0<modulus v := by simp [modulus,den]
  intro h
  have hmod : (2:Nat)^(K+1)%modulus v=offset v%modulus v := by
    rw [h, Nat.add_mod, Nat.mul_mod]
    simp
  have hreduced := pow_period_reduce (modulus v) period (K+1) hM hp hper
  rw [hreduced] at hmod
  exact hmiss ⟨(K+1)%period,Nat.mod_lt _ hp⟩ hmod

/-- First family (v=1) checked using period 12 modulo 35. -/
theorem sieve_v1 (q K : Nat) : ¬2^(K+1)=modulus 1*q+offset 1 := by
  have hmiss : ∀ r : Fin 12, 2^r.val%modulus 1 ≠ offset 1%modulus 1 := by decide +kernel
  exact period_sieve_excludes 1 12 (by decide) (by decide +kernel) hmiss q K

#print axioms pow_period_reduce
#print axioms period_sieve_excludes
#print axioms sieve_v1
end BB6.Agent48.NeedleTwoStepOdd
