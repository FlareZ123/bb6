import Std
set_option exponentiation.threshold 512

/-! Lean 4.36.0-rc2 finite modular gates for third-generation Sheep even exponents.
No theorem here claims entire TM halting or full machine-to-return-map equivalence. -/
namespace SheepThirdEvenA1

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

theorem allPow17Not11 (n : Nat) : 2^n % 17 ≠ 11 := by
  have he : n = (n%8)+8*(n/8) := by omega
  rw [he, periodPower 8 17 (n%8) (n/8) (by decide)]
  have hl : n%8 < 8 := Nat.mod_lt n (by decide)
  have cases : n%8=0 ∨ n%8=1 ∨ n%8=2 ∨ n%8=3 ∨ n%8=4 ∨ n%8=5 ∨ n%8=6 ∨ n%8=7 := by omega
  rcases cases with h | h | h | h | h | h | h | h <;> simp [h] <;> decide

theorem allPow43Not40 (n : Nat) : 2^n % 43 ≠ 40 := by
  have he : n = (n%14)+14*(n/14) := by omega
  rw [he, periodPower 14 43 (n%14) (n/14) (by decide)]
  have hl : n%14 < 14 := Nat.mod_lt n (by decide)
  have cases : n%14=0 ∨ n%14=1 ∨ n%14=2 ∨ n%14=3 ∨ n%14=4 ∨ n%14=5 ∨ n%14=6 ∨ n%14=7 ∨ n%14=8 ∨ n%14=9 ∨ n%14=10 ∨ n%14=11 ∨ n%14=12 ∨ n%14=13 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h] <;> decide

theorem allPow257Not199 (n : Nat) : 2^n % 257 ≠ 199 := by
  have he : n = (n%16)+16*(n/16) := by omega
  rw [he, periodPower 16 257 (n%16) (n/16) (by decide)]
  have hl : n%16 < 16 := Nat.mod_lt n (by decide)
  have cases : n%16=0 ∨ n%16=1 ∨ n%16=2 ∨ n%16=3 ∨ n%16=4 ∨ n%16=5 ∨ n%16=6 ∨ n%16=7 ∨ n%16=8 ∨ n%16=9 ∨ n%16=10 ∨ n%16=11 ∨ n%16=12 ∨ n%16=13 ∨ n%16=14 ∨ n%16=15 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h] <;> decide

theorem evenPower11Not10 (n : Nat) : 2^(2*n) % 11 ≠ 10 := by
  have he : 2*n = (2*(n%5))+10*(n/5) := by omega
  rw [he, periodPower 10 11 (2*(n%5)) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have cases : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
  rcases cases with h | h | h | h | h <;> simp [h] <;> decide

theorem evenPower11Not8 (n : Nat) : 2^(2*n) % 11 ≠ 8 := by
  have he : 2*n = (2*(n%5))+10*(n/5) := by omega
  rw [he, periodPower 10 11 (2*(n%5)) (n/5) (by decide)]
  have hl : n%5 < 5 := Nat.mod_lt n (by decide)
  have cases : n%5=0 ∨ n%5=1 ∨ n%5=2 ∨ n%5=3 ∨ n%5=4 := by omega
  rcases cases with h | h | h | h | h <;> simp [h] <;> decide

theorem fourPower17Not13 (n : Nat) : 2^(4*n) % 17 ≠ 13 := by
  have he : 4*n = (4*(n%2))+8*(n/2) := by omega
  rw [he, periodPower 8 17 (4*(n%2)) (n/2) (by decide)]
  have hcase : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hcase with h | h <;> simp [h] <;> decide

def smallGates (j : Nat) : Prop :=
  2^(j+4)%9 ≠ 7 ∧ 2^(j+4)%25 ≠ 19 ∧ 2^(j+4)%27 ≠ 22 ∧
  2^(j+4)%13 ≠ 9 ∧ 2^(j+2)%27 ≠ 7 ∧ 2^(j+2)%9 ≠ 4

theorem residue2 (q : Nat) : smallGates (2+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 2 4 q 7 (by decide) (by decide),
         periodNe 180 25 2 4 q 19 (by decide) (by decide),
         periodNe 180 27 2 4 q 22 (by decide) (by decide),
         periodNe 180 13 2 4 q 9 (by decide) (by decide),
         periodNe 180 27 2 2 q 7 (by decide) (by decide),
         periodNe 180 9 2 2 q 4 (by decide) (by decide)⟩

theorem residue22 (q : Nat) : smallGates (22+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 22 4 q 7 (by decide) (by decide),
         periodNe 180 25 22 4 q 19 (by decide) (by decide),
         periodNe 180 27 22 4 q 22 (by decide) (by decide),
         periodNe 180 13 22 4 q 9 (by decide) (by decide),
         periodNe 180 27 22 2 q 7 (by decide) (by decide),
         periodNe 180 9 22 2 q 4 (by decide) (by decide)⟩

theorem residue26 (q : Nat) : smallGates (26+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 26 4 q 7 (by decide) (by decide),
         periodNe 180 25 26 4 q 19 (by decide) (by decide),
         periodNe 180 27 26 4 q 22 (by decide) (by decide),
         periodNe 180 13 26 4 q 9 (by decide) (by decide),
         periodNe 180 27 26 2 q 7 (by decide) (by decide),
         periodNe 180 9 26 2 q 4 (by decide) (by decide)⟩

theorem residue38 (q : Nat) : smallGates (38+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 38 4 q 7 (by decide) (by decide),
         periodNe 180 25 38 4 q 19 (by decide) (by decide),
         periodNe 180 27 38 4 q 22 (by decide) (by decide),
         periodNe 180 13 38 4 q 9 (by decide) (by decide),
         periodNe 180 27 38 2 q 7 (by decide) (by decide),
         periodNe 180 9 38 2 q 4 (by decide) (by decide)⟩

theorem residue58 (q : Nat) : smallGates (58+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 58 4 q 7 (by decide) (by decide),
         periodNe 180 25 58 4 q 19 (by decide) (by decide),
         periodNe 180 27 58 4 q 22 (by decide) (by decide),
         periodNe 180 13 58 4 q 9 (by decide) (by decide),
         periodNe 180 27 58 2 q 7 (by decide) (by decide),
         periodNe 180 9 58 2 q 4 (by decide) (by decide)⟩

theorem residue62 (q : Nat) : smallGates (62+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 62 4 q 7 (by decide) (by decide),
         periodNe 180 25 62 4 q 19 (by decide) (by decide),
         periodNe 180 27 62 4 q 22 (by decide) (by decide),
         periodNe 180 13 62 4 q 9 (by decide) (by decide),
         periodNe 180 27 62 2 q 7 (by decide) (by decide),
         periodNe 180 9 62 2 q 4 (by decide) (by decide)⟩

theorem residue70 (q : Nat) : smallGates (70+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 70 4 q 7 (by decide) (by decide),
         periodNe 180 25 70 4 q 19 (by decide) (by decide),
         periodNe 180 27 70 4 q 22 (by decide) (by decide),
         periodNe 180 13 70 4 q 9 (by decide) (by decide),
         periodNe 180 27 70 2 q 7 (by decide) (by decide),
         periodNe 180 9 70 2 q 4 (by decide) (by decide)⟩

theorem residue98 (q : Nat) : smallGates (98+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 98 4 q 7 (by decide) (by decide),
         periodNe 180 25 98 4 q 19 (by decide) (by decide),
         periodNe 180 27 98 4 q 22 (by decide) (by decide),
         periodNe 180 13 98 4 q 9 (by decide) (by decide),
         periodNe 180 27 98 2 q 7 (by decide) (by decide),
         periodNe 180 9 98 2 q 4 (by decide) (by decide)⟩

theorem residue106 (q : Nat) : smallGates (106+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 106 4 q 7 (by decide) (by decide),
         periodNe 180 25 106 4 q 19 (by decide) (by decide),
         periodNe 180 27 106 4 q 22 (by decide) (by decide),
         periodNe 180 13 106 4 q 9 (by decide) (by decide),
         periodNe 180 27 106 2 q 7 (by decide) (by decide),
         periodNe 180 9 106 2 q 4 (by decide) (by decide)⟩

theorem residue110 (q : Nat) : smallGates (110+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 110 4 q 7 (by decide) (by decide),
         periodNe 180 25 110 4 q 19 (by decide) (by decide),
         periodNe 180 27 110 4 q 22 (by decide) (by decide),
         periodNe 180 13 110 4 q 9 (by decide) (by decide),
         periodNe 180 27 110 2 q 7 (by decide) (by decide),
         periodNe 180 9 110 2 q 4 (by decide) (by decide)⟩

theorem residue130 (q : Nat) : smallGates (130+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 130 4 q 7 (by decide) (by decide),
         periodNe 180 25 130 4 q 19 (by decide) (by decide),
         periodNe 180 27 130 4 q 22 (by decide) (by decide),
         periodNe 180 13 130 4 q 9 (by decide) (by decide),
         periodNe 180 27 130 2 q 7 (by decide) (by decide),
         periodNe 180 9 130 2 q 4 (by decide) (by decide)⟩

theorem residue142 (q : Nat) : smallGates (142+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 142 4 q 7 (by decide) (by decide),
         periodNe 180 25 142 4 q 19 (by decide) (by decide),
         periodNe 180 27 142 4 q 22 (by decide) (by decide),
         periodNe 180 13 142 4 q 9 (by decide) (by decide),
         periodNe 180 27 142 2 q 7 (by decide) (by decide),
         periodNe 180 9 142 2 q 4 (by decide) (by decide)⟩

theorem residue146 (q : Nat) : smallGates (146+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 146 4 q 7 (by decide) (by decide),
         periodNe 180 25 146 4 q 19 (by decide) (by decide),
         periodNe 180 27 146 4 q 22 (by decide) (by decide),
         periodNe 180 13 146 4 q 9 (by decide) (by decide),
         periodNe 180 27 146 2 q 7 (by decide) (by decide),
         periodNe 180 9 146 2 q 4 (by decide) (by decide)⟩

theorem residue166 (q : Nat) : smallGates (166+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 166 4 q 7 (by decide) (by decide),
         periodNe 180 25 166 4 q 19 (by decide) (by decide),
         periodNe 180 27 166 4 q 22 (by decide) (by decide),
         periodNe 180 13 166 4 q 9 (by decide) (by decide),
         periodNe 180 27 166 2 q 7 (by decide) (by decide),
         periodNe 180 9 166 2 q 4 (by decide) (by decide)⟩

theorem residue170 (q : Nat) : smallGates (170+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 170 4 q 7 (by decide) (by decide),
         periodNe 180 25 170 4 q 19 (by decide) (by decide),
         periodNe 180 27 170 4 q 22 (by decide) (by decide),
         periodNe 180 13 170 4 q 9 (by decide) (by decide),
         periodNe 180 27 170 2 q 7 (by decide) (by decide),
         periodNe 180 9 170 2 q 4 (by decide) (by decide)⟩

theorem residue178 (q : Nat) : smallGates (178+180*q) := by
  unfold smallGates
  exact ⟨periodNe 180 9 178 4 q 7 (by decide) (by decide),
         periodNe 180 25 178 4 q 19 (by decide) (by decide),
         periodNe 180 27 178 4 q 22 (by decide) (by decide),
         periodNe 180 13 178 4 q 9 (by decide) (by decide),
         periodNe 180 27 178 2 q 7 (by decide) (by decide),
         periodNe 180 9 178 2 q 4 (by decide) (by decide)⟩

theorem smallGates_all (j : Nat)
  (hj : j%180=2 ∨ j%180=22 ∨ j%180=26 ∨ j%180=38 ∨ j%180=58 ∨ j%180=62 ∨ j%180=70 ∨ j%180=98 ∨ j%180=106 ∨ j%180=110 ∨ j%180=130 ∨ j%180=142 ∨ j%180=146 ∨ j%180=166 ∨ j%180=170 ∨ j%180=178) : smallGates j := by
  rcases hj with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have eq : j=2+180*(j/180) := by omega
    rw [eq]
    exact residue2 (j/180)
  · have eq : j=22+180*(j/180) := by omega
    rw [eq]
    exact residue22 (j/180)
  · have eq : j=26+180*(j/180) := by omega
    rw [eq]
    exact residue26 (j/180)
  · have eq : j=38+180*(j/180) := by omega
    rw [eq]
    exact residue38 (j/180)
  · have eq : j=58+180*(j/180) := by omega
    rw [eq]
    exact residue58 (j/180)
  · have eq : j=62+180*(j/180) := by omega
    rw [eq]
    exact residue62 (j/180)
  · have eq : j=70+180*(j/180) := by omega
    rw [eq]
    exact residue70 (j/180)
  · have eq : j=98+180*(j/180) := by omega
    rw [eq]
    exact residue98 (j/180)
  · have eq : j=106+180*(j/180) := by omega
    rw [eq]
    exact residue106 (j/180)
  · have eq : j=110+180*(j/180) := by omega
    rw [eq]
    exact residue110 (j/180)
  · have eq : j=130+180*(j/180) := by omega
    rw [eq]
    exact residue130 (j/180)
  · have eq : j=142+180*(j/180) := by omega
    rw [eq]
    exact residue142 (j/180)
  · have eq : j=146+180*(j/180) := by omega
    rw [eq]
    exact residue146 (j/180)
  · have eq : j=166+180*(j/180) := by omega
    rw [eq]
    exact residue166 (j/180)
  · have eq : j=170+180*(j/180) := by omega
    rw [eq]
    exact residue170 (j/180)
  · have eq : j=178+180*(j/180) := by omega
    rw [eq]
    exact residue178 (j/180)

#print axioms smallGates_all
#print axioms evenPower11Not8
#print axioms fourPower17Not13
#print axioms evenPower11Not10
#print axioms allPow17Not11
#print axioms allPow43Not40
#print axioms allPow257Not199
end SheepThirdEvenA1
