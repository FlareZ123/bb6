import Lean.Elab.Tactic.Omega
namespace BB6.Agent37EChainResidues

/-- One plus a multiple of three, for every 64-power. -/
theorem power64_linear (n : Nat) : ∃ t : Nat, 64^n = 3*t+1 := by
  induction n with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨64*t+21,?_⟩
    rw [Nat.pow_succ, ht]
    omega

private theorem power8_even (n : Nat) : 8^(2*n) = 64^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+2 by omega, Nat.pow_add, ih]
    rw [Nat.pow_succ]
    simp [Nat.pow_succ]

private theorem power8_odd (n : Nat) : 8^(2*n+1) = 8*(64^n) := by
  rw [Nat.pow_succ, power8_even]
  ac_rfl

/-- After 2n guarded E packets, h=3s+2 gives an A unary prefix. -/
theorem even_A_index (n s : Nat) :
    ∃ ka : Nat, 1+4*8^(2*n)*(3*s+2) = 3*ka+3 := by
  obtain ⟨t,ht⟩ := power64_linear n
  refine ⟨12*t*s+8*t+4*s+2,?_⟩
  rw [power8_even,ht]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  rw [show t*(3*s)=3*(t*s) by ac_rfl]
  omega

/-- After 2n+1 guarded E packets, h=3s+1 gives an A unary prefix. -/
theorem odd_A_index (n s : Nat) :
    ∃ ka : Nat, 1+4*8^(2*n+1)*(3*s+1) = 3*ka+3 := by
  obtain ⟨t,ht⟩ := power64_linear n
  refine ⟨96*t*s+32*t+32*s+10,?_⟩
  rw [power8_odd,ht]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  rw [show t*(3*s)=3*(t*s) by ac_rfl]
  omega

/-- A division-free residue index for the fixed-tail reset. -/
def half9 : Nat → Nat
  | 0 => 0
  | n+1 => 9*half9 n+4

theorem half9_pow (n : Nat) : 9^n = 2*half9 n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, ih]
    simp only [half9]
    omega

private theorem pow3_even (n : Nat) : 3^(2*n)=9^n := by
  rw [Nat.pow_mul]

private theorem pow3_odd (n : Nat) : 3^(2*n+1)=3*9^n := by
  rw [Nat.pow_succ, pow3_even]
  ac_rfl

def evenK (n s : Nat) := 3*9^n*s+5*half9 n+2
def oddK (n s : Nat) := 9*9^n*s+3*half9 n+1

theorem evenK_root (n s : Nat) :
    2*evenK n s+1 = 3^(2*n)*(6*s+5) := by
  unfold evenK
  rw [pow3_even,half9_pow]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  rw [show half9 n*(6*s)=6*(half9 n*s) by ac_rfl]
  omega

theorem oddK_root (n s : Nat) :
    2*oddK n s+1 = 3^(2*n+1)*(6*s+1) := by
  unfold oddK
  rw [pow3_odd,half9_pow]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
  rw [show half9 n*(6*s)=6*(half9 n*s) by ac_rfl]
  omega

#print axioms half9_pow
#print axioms evenK_root
#print axioms oddK_root
#print axioms power64_linear
#print axioms even_A_index
#print axioms odd_A_index
end BB6.Agent37EChainResidues
