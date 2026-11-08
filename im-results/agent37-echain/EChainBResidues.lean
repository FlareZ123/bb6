import Lean.Elab.Tactic.Omega
import EChainResidues

namespace BB6.Agent37EChainBResidues
open BB6.Agent37EChainResidues

theorem power64_mod9 (n : Nat) : ∃ t, 64^n = 9*t+1 := by
  induction n with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨64*t+7,?_⟩
    rw [Nat.pow_succ,ht]
    omega

private theorem power8_even (n : Nat) : 8^(2*n)=64^n := by
  rw [Nat.pow_mul]

private theorem power8_odd (n : Nat) : 8^(2*n+1)=8*64^n := by
  rw [Nat.pow_succ,power8_even]
  ac_rfl

/-- After an even number of E calls, h=9s+1 admits a B then A exit. -/
theorem even_BA_index (n s : Nat) :
    ∃ kb ka : Nat,
      1+4*8^(2*n)*(9*s+1)=3*kb+2 ∧
      8*kb+10=3*ka+3 := by
  obtain ⟨t,ht⟩ := power64_mod9 n
  refine ⟨108*t*s+12*t+12*s+1,288*t*s+32*t+32*s+5,?_,?_⟩
  · rw [power8_even,ht]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
    rw [show t*(9*s)=9*(t*s) by ac_rfl]
    omega
  · simp only [Nat.mul_assoc]
    omega

/-- After an odd number of E calls, h=9s+8 admits a B then A exit. -/
theorem odd_BA_index (n s : Nat) :
    ∃ kb ka : Nat,
      1+4*8^(2*n+1)*(9*s+8)=3*kb+2 ∧
      8*kb+10=3*ka+3 := by
  obtain ⟨t,ht⟩ := power64_mod9 n
  refine ⟨864*t*s+768*t+96*s+85,2304*t*s+2048*t+256*s+229,?_,?_⟩
  · rw [power8_odd,ht]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
    rw [show t*(9*s)=9*(t*s) by ac_rfl]
    omega
  · simp only [Nat.mul_assoc]
    omega

/-- Division-free k indices that make the E,p=2 reset B->A. -/
def evenBK (n s : Nat) := 9*9^n*s+half9 n
def oddBK (n s : Nat) := 27*9^n*s+51*half9 n+25

private theorem pow3_even (n : Nat) : 3^(2*n)=9^n := by
  rw [Nat.pow_mul]

private theorem pow3_odd (n : Nat) : 3^(2*n+1)=3*9^n := by
  rw [Nat.pow_succ,pow3_even]
  ac_rfl

theorem evenBK_root (n s : Nat) :
    2*evenBK n s+1 = 3^(2*n)*(18*s+1) := by
  unfold evenBK
  rw [pow3_even,half9_pow]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  rw [show half9 n*(18*s)=18*(half9 n*s) by ac_rfl]
  omega

theorem oddBK_root (n s : Nat) :
    2*oddBK n s+1 = 3^(2*n+1)*(18*s+17) := by
  unfold oddBK
  rw [pow3_odd,half9_pow]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  rw [show half9 n*(18*s)=18*(half9 n*s) by ac_rfl]
  omega

#print axioms power64_mod9
#print axioms even_BA_index
#print axioms odd_BA_index
#print axioms evenBK_root
#print axioms oddBK_root
end BB6.Agent37EChainBResidues
