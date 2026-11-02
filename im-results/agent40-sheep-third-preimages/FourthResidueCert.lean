import Std
set_option exponentiation.threshold 700

/-! Fourth-generation Sheep preimage gates, universal on j modulo648. -/
namespace SheepFourth

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

theorem allPow43Not3 (n : Nat) : 2^n % 43 ≠ 3 := by
  have he : n = (n%14)+14*(n/14) := by omega
  rw [he, periodPower 14 43 (n%14) (n/14) (by decide)]
  have hl : n%14 < 14 := Nat.mod_lt n (by decide)
  have cases : n%14=0 ∨ n%14=1 ∨ n%14=2 ∨ n%14=3 ∨ n%14=4 ∨ n%14=5 ∨ n%14=6 ∨ n%14=7 ∨ n%14=8 ∨ n%14=9 ∨ n%14=10 ∨ n%14=11 ∨ n%14=12 ∨ n%14=13 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h] <;> decide

theorem allPow257Not56 (n : Nat) : 2^n % 257 ≠ 56 := by
  have he : n = (n%16)+16*(n/16) := by omega
  rw [he, periodPower 16 257 (n%16) (n/16) (by decide)]
  have hl : n%16 < 16 := Nat.mod_lt n (by decide)
  have cases : n%16=0 ∨ n%16=1 ∨ n%16=2 ∨ n%16=3 ∨ n%16=4 ∨ n%16=5 ∨ n%16=6 ∨ n%16=7 ∨ n%16=8 ∨ n%16=9 ∨ n%16=10 ∨ n%16=11 ∨ n%16=12 ∨ n%16=13 ∨ n%16=14 ∨ n%16=15 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h] <;> decide

theorem evenPower11Not8 (n : Nat) : 2^(2*n) % 11 ≠ 8 := by
  have he : 2*n = (2*(n%5)+0)+10*(n/5) := by omega
  rw [he, periodPower 10 11 (2*(n%5)+0) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have cases : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
  rcases cases with h | h | h | h | h <;> simp [h] <;> decide

theorem oddPower11Not9 (n : Nat) : 2^(2*n+1) % 11 ≠ 9 := by
  have he : 2*n+1 = (2*(n%5)+1)+10*(n/5) := by omega
  rw [he, periodPower 10 11 (2*(n%5)+1) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have cases : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
  rcases cases with h | h | h | h | h <;> simp [h] <;> decide

def smallGates (j : Nat) : Prop :=
  2^(j+4)%81 ≠ 16 ∧ 2^(j+4)%5 ≠ 4 ∧ 2^(j+4)%243 ≠ 43 ∧ 2^(j+4)%17 ≠ 12 ∧ 2^(j+4)%13 ≠ 10 ∧ 2^(j+4)%19 ≠ 6 ∧ 2^(j+3)%5 ≠ 4 ∧ 2^(j+3)%81 ≠ 17 ∧ 2^(j+3)%17 ≠ 1 ∧ 2^(j+3)%5 ≠ 1 ∧ 2^(j+2)%5 ≠ 1 ∧ 2^(j+2)%27 ≠ 7 ∧ 2^(j+2)%17 ≠ 13 ∧ 2^(j+1)%5 ≠ 1

theorem residue72 (q : Nat) : smallGates (72+648*q) := by
  unfold smallGates
  exact ⟨periodNe 648 81 72 4 q 16 (by decide) (by decide),
         periodNe 648 5 72 4 q 4 (by decide) (by decide),
         periodNe 648 243 72 4 q 43 (by decide) (by decide),
         periodNe 648 17 72 4 q 12 (by decide) (by decide),
         periodNe 648 13 72 4 q 10 (by decide) (by decide),
         periodNe 648 19 72 4 q 6 (by decide) (by decide),
         periodNe 648 5 72 3 q 4 (by decide) (by decide),
         periodNe 648 81 72 3 q 17 (by decide) (by decide),
         periodNe 648 17 72 3 q 1 (by decide) (by decide),
         periodNe 648 5 72 3 q 1 (by decide) (by decide),
         periodNe 648 5 72 2 q 1 (by decide) (by decide),
         periodNe 648 27 72 2 q 7 (by decide) (by decide),
         periodNe 648 17 72 2 q 13 (by decide) (by decide),
         periodNe 648 5 72 1 q 1 (by decide) (by decide)⟩

theorem residue144 (q : Nat) : smallGates (144+648*q) := by
  unfold smallGates
  exact ⟨periodNe 648 81 144 4 q 16 (by decide) (by decide),
         periodNe 648 5 144 4 q 4 (by decide) (by decide),
         periodNe 648 243 144 4 q 43 (by decide) (by decide),
         periodNe 648 17 144 4 q 12 (by decide) (by decide),
         periodNe 648 13 144 4 q 10 (by decide) (by decide),
         periodNe 648 19 144 4 q 6 (by decide) (by decide),
         periodNe 648 5 144 3 q 4 (by decide) (by decide),
         periodNe 648 81 144 3 q 17 (by decide) (by decide),
         periodNe 648 17 144 3 q 1 (by decide) (by decide),
         periodNe 648 5 144 3 q 1 (by decide) (by decide),
         periodNe 648 5 144 2 q 1 (by decide) (by decide),
         periodNe 648 27 144 2 q 7 (by decide) (by decide),
         periodNe 648 17 144 2 q 13 (by decide) (by decide),
         periodNe 648 5 144 1 q 1 (by decide) (by decide)⟩

theorem residue360 (q : Nat) : smallGates (360+648*q) := by
  unfold smallGates
  exact ⟨periodNe 648 81 360 4 q 16 (by decide) (by decide),
         periodNe 648 5 360 4 q 4 (by decide) (by decide),
         periodNe 648 243 360 4 q 43 (by decide) (by decide),
         periodNe 648 17 360 4 q 12 (by decide) (by decide),
         periodNe 648 13 360 4 q 10 (by decide) (by decide),
         periodNe 648 19 360 4 q 6 (by decide) (by decide),
         periodNe 648 5 360 3 q 4 (by decide) (by decide),
         periodNe 648 81 360 3 q 17 (by decide) (by decide),
         periodNe 648 17 360 3 q 1 (by decide) (by decide),
         periodNe 648 5 360 3 q 1 (by decide) (by decide),
         periodNe 648 5 360 2 q 1 (by decide) (by decide),
         periodNe 648 27 360 2 q 7 (by decide) (by decide),
         periodNe 648 17 360 2 q 13 (by decide) (by decide),
         periodNe 648 5 360 1 q 1 (by decide) (by decide)⟩

theorem residue504 (q : Nat) : smallGates (504+648*q) := by
  unfold smallGates
  exact ⟨periodNe 648 81 504 4 q 16 (by decide) (by decide),
         periodNe 648 5 504 4 q 4 (by decide) (by decide),
         periodNe 648 243 504 4 q 43 (by decide) (by decide),
         periodNe 648 17 504 4 q 12 (by decide) (by decide),
         periodNe 648 13 504 4 q 10 (by decide) (by decide),
         periodNe 648 19 504 4 q 6 (by decide) (by decide),
         periodNe 648 5 504 3 q 4 (by decide) (by decide),
         periodNe 648 81 504 3 q 17 (by decide) (by decide),
         periodNe 648 17 504 3 q 1 (by decide) (by decide),
         periodNe 648 5 504 3 q 1 (by decide) (by decide),
         periodNe 648 5 504 2 q 1 (by decide) (by decide),
         periodNe 648 27 504 2 q 7 (by decide) (by decide),
         periodNe 648 17 504 2 q 13 (by decide) (by decide),
         periodNe 648 5 504 1 q 1 (by decide) (by decide)⟩

theorem residue576 (q : Nat) : smallGates (576+648*q) := by
  unfold smallGates
  exact ⟨periodNe 648 81 576 4 q 16 (by decide) (by decide),
         periodNe 648 5 576 4 q 4 (by decide) (by decide),
         periodNe 648 243 576 4 q 43 (by decide) (by decide),
         periodNe 648 17 576 4 q 12 (by decide) (by decide),
         periodNe 648 13 576 4 q 10 (by decide) (by decide),
         periodNe 648 19 576 4 q 6 (by decide) (by decide),
         periodNe 648 5 576 3 q 4 (by decide) (by decide),
         periodNe 648 81 576 3 q 17 (by decide) (by decide),
         periodNe 648 17 576 3 q 1 (by decide) (by decide),
         periodNe 648 5 576 3 q 1 (by decide) (by decide),
         periodNe 648 5 576 2 q 1 (by decide) (by decide),
         periodNe 648 27 576 2 q 7 (by decide) (by decide),
         periodNe 648 17 576 2 q 13 (by decide) (by decide),
         periodNe 648 5 576 1 q 1 (by decide) (by decide)⟩

theorem smallGates_all (j : Nat)
    (hj : j%648=72 ∨ j%648=144 ∨ j%648=360 ∨ j%648=504 ∨ j%648=576) : smallGates j := by
  rcases hj with h | h | h | h | h
  · have eq : j=72+648*(j/648) := by omega
    rw [eq]
    exact residue72 (j/648)
  · have eq : j=144+648*(j/648) := by omega
    rw [eq]
    exact residue144 (j/648)
  · have eq : j=360+648*(j/648) := by omega
    rw [eq]
    exact residue360 (j/648)
  · have eq : j=504+648*(j/648) := by omega
    rw [eq]
    exact residue504 (j/648)
  · have eq : j=576+648*(j/648) := by omega
    rw [eq]
    exact residue576 (j/648)

#print axioms smallGates_all
#print axioms allPow43Not3
#print axioms allPow257Not56
#print axioms evenPower11Not8
#print axioms oddPower11Not9
end SheepFourth
