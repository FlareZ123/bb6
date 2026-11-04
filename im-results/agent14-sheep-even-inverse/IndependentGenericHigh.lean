import Std

namespace SheepIndependentGenericHigh

/-- Signed remainder in the exact generic Sheep inverse equation. -/
def K (D : Nat) (C : Int) (a : Nat) : Int :=
  (D:Int)*(2*(a:Int)-1)-2*C

private theorem K_succ (D : Nat) (C : Int) (a : Nat) :
    K D C (a+1) = K D C a + 2*(D:Int) := by
  simp only [K, Int.natCast_add, Int.ofNat_one]
  rw [show 2*((a:Int)+1)-1 = (2*(a:Int)-1)+2 by omega, Int.mul_add]
  omega

/-- The base integer inequality automatically propagates to every larger
2-adic valuation because K grows linearly and powers of 2 double. -/
theorem high_all (D A : Nat) (C : Int)
    (hbase : (1:Int) < K D C A ∧ (K D C A)%2=1 ∧
      K D C A < (2:Int)^A ∧ (2*(D:Int)) ≤ (2:Int)^A) :
    ∀ a : Nat, A≤a →
      (1:Int)<K D C a ∧ K D C a%2=1 ∧
      K D C a < (2:Int)^a ∧ 2*(D:Int) ≤ (2:Int)^a := by
  intro a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have hs : K D C (A+(k+1))=K D C (A+k)+2*(D:Int) := by
      simpa only [show A+(k+1)=A+k+1 by omega] using K_succ D C (A+k)
    have hp : (2:Int)^(A+(k+1))=2*(2:Int)^(A+k) := by
      rw [show A+(k+1)=A+k+1 by omega,Int.pow_succ]
      rw [Int.mul_comm]
    have hd : 0≤(D:Int) := by exact_mod_cast Nat.zero_le D
    rw [hs,hp]
    rcases ih (by omega) with ⟨hlo,hodd,hhi,hD⟩
    constructor
    · omega
    constructor
    · omega
    constructor
    · omega
    · omega

#print axioms high_all
end SheepIndependentGenericHigh
