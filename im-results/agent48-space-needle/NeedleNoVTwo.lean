import NeedleTwoStepOdd
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.NeedleTwoStepOdd

private theorem power_twenty_mod_55 (q : Nat) : ((2:Nat)^20)^q%55=1 := by
  induction q with
  | zero => decide
  | succ q ih =>
      rw [Nat.pow_succ',Nat.mul_mod,ih]

private theorem pow_mod55_reduce (k : Nat) :
    (2:Nat)^k%55 = 2^(k%20)%55 := by
  let q:=k/20
  have heq : k=20*q+k%20 := by dsimp[q]; omega
  rw [heq,Nat.pow_add,Nat.mul_mod]
  have hpow : (2:Nat)^(20*q) = (2^20)^q := by rw [Nat.pow_mul]
  rw [hpow,power_twenty_mod_55]
  simp

/-- The residue 27 never occurs among powers of two modulo 55. -/
theorem two_pow_not_27_mod55 (k : Nat) : (2:Nat)^k%55 ≠ 27 := by
  rw [pow_mod55_reduce k]
  have hs : ∀ r : Fin 20, (2:Nat)^r.val%55≠27 := by decide +kernel
  exact hs ⟨k%20,Nat.mod_lt _ (by decide)⟩

/-- First-step valuation two cannot feed any odd-ending terminal second step. -/
theorem no_v_two_odd_terminal (q K : Nat) :
    ¬ 2^(K+1)=modulus 2*q+offset 2 := by
  intro h
  have he : 2^(K+1)=55*q+82 := by
    simpa [modulus,den,offset] using h
  have hmod : 2^(K+1)%55=27 := by rw [he]; omega
  exact two_pow_not_27_mod55 (K+1) hmod

#print axioms two_pow_not_27_mod55
#print axioms no_v_two_odd_terminal
end BB6.Agent48.NeedleTwoStepOdd
