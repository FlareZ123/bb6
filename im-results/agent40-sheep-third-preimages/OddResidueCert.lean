import Std
set_option exponentiation.threshold 512

/-! Standalone Lean 4.36.0-rc2 modular certificate for seven Sheep depth-three inverse classes.
The handwritten general residue-gap and exceptional-branch proofs are in ODD-CLASSES.md. -/
namespace SheepThirdOdd

private theorem periodPower (period m r q : Nat) (hp : 2^period % m = 1) :
    2^(r+period*q) % m = 2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^period) q m, hp]
  simp

private theorem periodNe (period m r k q target : Nat)
    (hp : 2^period % m = 1) (hb : 2^(r+k) % m ≠ target) :
    2^(r+period*q+k) % m ≠ target := by
  rw [show r+period*q+k = (r+k)+period*q by omega,
      periodPower period m (r+k) q hp]
  exact hb

theorem evenPowerMod3 (n : Nat) : 2^(2*n) % 3 = 1 := by
  rw [show 2*n=0+2*n by omega, periodPower 2 3 0 n (by decide)]

theorem evenPower17Not8 (n : Nat) : 2^(2*n) % 17 ≠ 8 := by
  have he : 2*n = (2*(n%4))+8*(n/4) := by omega
  rw [he, periodPower 8 17 (2*(n%4)) (n/4) (by decide)]
  have hl : n%4 < 4 := Nat.mod_lt n (by decide)
  have cases : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
  rcases cases with h | h | h | h <;> simp [h] <;> decide

theorem evenPower11Not2 (n : Nat) : 2^(2*n) % 11 ≠ 2 := by
  have he : 2*n = (2*(n%5))+10*(n/5) := by omega
  rw [he, periodPower 10 11 (2*(n%5)) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have cases : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
  rcases cases with h | h | h | h | h <;> simp [h] <;> decide

theorem power257Not104 (n : Nat) : 2^n % 257 ≠ 104 := by
  have he : n = (n%16)+16*(n/16) := by omega
  rw [he, periodPower 16 257 (n%16) (n/16) (by decide)]
  have hl : n%16 < 16 := Nat.mod_lt n (by decide)
  have cases : n%16=0 ∨ n%16=1 ∨ n%16=2 ∨ n%16=3 ∨ n%16=4 ∨ n%16=5 ∨ n%16=6 ∨ n%16=7 ∨ n%16=8 ∨ n%16=9 ∨ n%16=10 ∨ n%16=11 ∨ n%16=12 ∨ n%16=13 ∨ n%16=14 ∨ n%16=15 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h] <;> decide

def oddSmallGates (j : Nat) : Prop :=
  2^(j+5) % 125 ≠ 61 ∧ 2^(j+5) % 1625 ≠ 261

theorem residue11 (q : Nat) : oddSmallGates (11+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 11 5 q 61 (by decide) (by decide),
         periodNe 300 1625 11 5 q 261 (by decide) (by decide)⟩

theorem residue31 (q : Nat) : oddSmallGates (31+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 31 5 q 61 (by decide) (by decide),
         periodNe 300 1625 31 5 q 261 (by decide) (by decide)⟩

theorem residue71 (q : Nat) : oddSmallGates (71+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 71 5 q 61 (by decide) (by decide),
         periodNe 300 1625 71 5 q 261 (by decide) (by decide)⟩

theorem residue91 (q : Nat) : oddSmallGates (91+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 91 5 q 61 (by decide) (by decide),
         periodNe 300 1625 91 5 q 261 (by decide) (by decide)⟩

theorem residue131 (q : Nat) : oddSmallGates (131+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 131 5 q 61 (by decide) (by decide),
         periodNe 300 1625 131 5 q 261 (by decide) (by decide)⟩

theorem residue191 (q : Nat) : oddSmallGates (191+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 191 5 q 61 (by decide) (by decide),
         periodNe 300 1625 191 5 q 261 (by decide) (by decide)⟩

theorem residue211 (q : Nat) : oddSmallGates (211+300*q) := by
  unfold oddSmallGates
  exact ⟨periodNe 300 125 211 5 q 61 (by decide) (by decide),
         periodNe 300 1625 211 5 q 261 (by decide) (by decide)⟩

theorem oddSmallGates_all (j : Nat)
  (hj : j%300=11 ∨ j%300=31 ∨ j%300=71 ∨ j%300=91 ∨
        j%300=131 ∨ j%300=191 ∨ j%300=211) : oddSmallGates j := by
  rcases hj with h | h | h | h | h | h | h
  · have eq : j=11+300*(j/300) := by omega
    rw [eq]
    exact residue11 (j/300)
  · have eq : j=31+300*(j/300) := by omega
    rw [eq]
    exact residue31 (j/300)
  · have eq : j=71+300*(j/300) := by omega
    rw [eq]
    exact residue71 (j/300)
  · have eq : j=91+300*(j/300) := by omega
    rw [eq]
    exact residue91 (j/300)
  · have eq : j=131+300*(j/300) := by omega
    rw [eq]
    exact residue131 (j/300)
  · have eq : j=191+300*(j/300) := by omega
    rw [eq]
    exact residue191 (j/300)
  · have eq : j=211+300*(j/300) := by omega
    rw [eq]
    exact residue211 (j/300)

#print axioms oddSmallGates_all
#print axioms evenPowerMod3
#print axioms evenPower17Not8
#print axioms evenPower11Not2
#print axioms power257Not104
end SheepThirdOdd
