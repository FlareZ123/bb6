import Std

namespace SheepChain2

/-- A genuine generic Sheep first-even return with source 4*v (v odd >=5). -/
def Parent2 (x y : Nat) : Prop :=
  20 ≤ x ∧ x % 8 = 4 ∧ 9*x+12=8*y

inductive Chain2 : Nat → Nat → Nat → Prop where
  | nil (x : Nat) : Chain2 0 x x
  | cons {n x y z : Nat} (edge : Parent2 x y)
      (tail : Chain2 n y z) : Chain2 (n+1) x z

private theorem parent_offset {x y : Nat} (h : Parent2 x y) :
    9*(x+12)=8*(y+12) := by
  obtain ⟨_, _, he⟩ := h
  omega

theorem chain_offset {n x y : Nat} (c : Chain2 n x y) :
    9^n * (x+12) = 8^n * (y+12) := by
  induction c with
  | nil x => simp
  | @cons n x y z edge tail ih =>
      have he := parent_offset edge
      calc
        9^(n+1)*(x+12) = 9^n*(9*(x+12)) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ = 9^n*(8*(y+12)) := by rw [he]
        _ = 8*(9^n*(y+12)) := by ac_rfl
        _ = 8*(8^n*(z+12)) := by rw [ih]
        _ = 8^(n+1)*(z+12) := by
          rw [Nat.pow_succ]
          ac_rfl

theorem chain_divisible {n x y : Nat} (c : Chain2 n x y) :
    9^n ∣ y+12 := by
  have hc := chain_offset c
  have hd : 9^n ∣ 8^n * (y+12) := ⟨x+12, hc.symm⟩
  have hcop : Nat.Coprime (9^n) (8^n) := by
    exact (by decide : Nat.Coprime 9 8).pow n n
  exact hcop.dvd_of_dvd_mul_left hd

private theorem parent_explicit (m : Nat) (hm : 4 ≤ m) :
    Parent2 (8*m-12) (9*m-12) := by
  unfold Parent2
  constructor
  · omega
  constructor
  · have he : 8*m-12=8*(m-2)+4 := by omega
    rw [he]
    omega
  · omega

theorem chain_from_factor (n : Nat) : ∀ m : Nat, 4 ≤ m →
    Chain2 n (8^n*m-12) (9^n*m-12) := by
  induction n with
  | zero =>
      intro m hm
      simpa using Chain2.nil (m-12)
  | succ n ih =>
      intro m hm
      have hp : 1 ≤ 8^n := by
        have : 0 < 8^n := Nat.pow_pos (by decide : 0<8)
        omega
      have hmult := Nat.mul_le_mul_right m hp
      have hm8 : 4 ≤ 8^n*m := by omega
      have hm9 : 4 ≤ 9*m := by omega
      have edge := parent_explicit (8^n*m) hm8
      have tail := ih (9*m) hm9
      have hchain : Chain2 (n+1) (8*(8^n*m)-12) (9^n*(9*m)-12) := by
        apply Chain2.cons edge
        simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using tail
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        using hchain

#print axioms chain_from_factor
#print axioms chain_divisible
end SheepChain2
