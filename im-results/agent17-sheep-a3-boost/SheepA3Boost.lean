import Std
namespace SheepA3Boost

private theorem pow4_nine (s : Nat) : (4:Nat)^(9^s) % 17 = 4 := by
  induction s with
  | zero => decide
  | succ s ih =>
    calc
      (4:Nat)^(9^(s+1)) % 17 = ((4:Nat)^(9^s))^9 % 17 := by
        rw [Nat.pow_succ, Nat.pow_mul]
      _ = ((4^(9^s) % 17)^9) % 17 := by rw [Nat.pow_mod]
      _ = 4 := by rw [ih]

private theorem pow4_three_nine (s : Nat) : (4:Nat)^(3*9^s) % 17 = 13 := by
  calc
    (4:Nat)^(3*9^s) % 17 = ((4:Nat)^(9^s))^3 % 17 := by
      rw [Nat.mul_comm, Nat.pow_mul]
    _ = ((4^(9^s) % 17)^3) % 17 := by rw [Nat.pow_mod]
    _ = 13 := by rw [pow4_nine]

private theorem target_even_mod (s : Nat) : (2:Nat)^(2*9^s) % 17 = 4 := by
  rw [Nat.pow_mul]
  exact pow4_nine s

private theorem target_odd_mod (s : Nat) : (2:Nat)^(2*(3*9^s)) % 17 = 13 := by
  rw [Nat.pow_mul]
  exact pow4_three_nine s

private theorem pow_period16 (a h : Nat) (ha : a^16 % 17 = 1) :
    a^h % 17 = a^(h%16) % 17 := by
  have hd : h = 16*(h/16)+h%16 := by
    have := Nat.mod_add_div h 16
    omega
  calc
    a^h % 17 = a^(16*(h/16)+h%16) % 17 := congrArg (fun e : Nat => a^e%17) hd
    _ = (a^(16*(h/16))*a^(h%16))%17 := by rw [Nat.pow_add]
    _ = ((a^(16*(h/16))%17)*(a^(h%16)%17))%17 := by rw [Nat.mul_mod]
    _ = a^(h%16)%17 := by
      rw [Nat.pow_mul, Nat.pow_mod, ha]
      simp

private theorem pow_period16_succ (a h : Nat) (ha : a^16%17=1) :
    a^(h+1)%17 = a^((h%16)+1)%17 := by
  have hd : h = 16*(h/16)+h%16 := by
    have := Nat.mod_add_div h 16
    omega
  calc
    a^(h+1)%17 = a^(16*(h/16)+(h%16+1))%17 := by
      have he : h+1 = 16*(h/16)+(h%16+1) := by omega
      rw [he]
    _ = (a^(16*(h/16))*a^(h%16+1))%17 := by rw [Nat.pow_add]
    _ = ((a^(16*(h/16))%17)*(a^(h%16+1)%17))%17 := by rw [Nat.mul_mod]
    _ = a^(h%16+1)%17 := by
      rw [Nat.pow_mul, Nat.pow_mod, ha]
      simp

-- Exact classification of the possible valuation-three source lengths.
theorem mod_iff_even (s h q : Nat)
    (hq : 3^h*q+1 = 2^(2*9^s)) :
    ((2:Nat)^(h+1)*q)%17=3 ↔ h%16=10 := by
  have hm := congrArg (fun x : Nat => x%17) hq
  rw [Nat.add_mod, Nat.mul_mod, target_even_mod] at hm
  rw [Nat.mul_mod, pow_period16_succ 2 h (by decide)]
  have h3 : (3:Nat)^h%17 = 3^(h%16)%17 := pow_period16 3 h (by decide)
  rw [h3] at hm
  have hall : ∀ r : Fin 16, ∀ z : Fin 17,
    (((3:Nat)^r.val%17*z.val)%17+1)%17=4 →
      (((2:Nat)^(r.val+1)%17*z.val)%17=3 ↔ r.val=10) := by decide
  exact hall ⟨h%16, Nat.mod_lt h (by decide)⟩
    ⟨q%17, Nat.mod_lt q (by decide)⟩ hm

theorem mod_iff_odd (s h q : Nat)
    (hq : 3^h*q+1 = 2^(2*(3*9^s))) :
    ((2:Nat)^(h+1)*q)%17=3 ↔ h%16=14 := by
  have hm := congrArg (fun x : Nat => x%17) hq
  rw [Nat.add_mod, Nat.mul_mod, target_odd_mod] at hm
  rw [Nat.mul_mod, pow_period16_succ 2 h (by decide)]
  have h3 : (3:Nat)^h%17 = 3^(h%16)%17 := pow_period16 3 h (by decide)
  rw [h3] at hm
  have hall : ∀ r : Fin 16, ∀ z : Fin 17,
    (((3:Nat)^r.val%17*z.val)%17+1)%17=13 →
      (((2:Nat)^(r.val+1)%17*z.val)%17=3 ↔ r.val=14) := by decide
  exact hall ⟨h%16, Nat.mod_lt h (by decide)⟩
    ⟨q%17, Nat.mod_lt q (by decide)⟩ hm

-- Recover the exact legal odd cofactor from a modular parent condition.
theorem parent_arithmetic (h q : Nat) (hh : 4 ≤ h) (hq : 7 ≤ q)
    (hm : ((2:Nat)^(h+1)*q)%17 = 3) :
    ∃ v : Nat, 5 ≤ v ∧ v%2=1 ∧ 17*v+3=2^(h+1)*q := by
  let P := 2^(h+1)*q
  have hpow : 32 ≤ 2^(h+1) := by
    have hp := Nat.pow_le_pow_right (n:=2) (by decide) (show 5 ≤ h+1 by omega)
    simpa using hp
  have hprod : 224 ≤ P := by
    dsimp [P]
    have := Nat.mul_le_mul hpow hq
    omega
  have heven : P%2=0 := by
    dsimp [P]
    rw [Nat.mul_mod, Nat.pow_succ, Nat.mul_mod]
    simp
  have hdec : P%17+17*(P/17)=P := Nat.mod_add_div P 17
  refine ⟨P/17, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega

-- Explicit infinite-family certificates, conditional only on the
-- elementary 3-adic divisibility identity and lower cofactor bound.
theorem parent_even (s t q : Nat)
    (hq : 3^(16*t+10)*q+1 = 2^(2*9^s)) (hqmin : 7 ≤ q) :
    ∃ v : Nat, 5 ≤ v ∧ v%2=1 ∧ 17*v+3=2^(16*t+11)*q := by
  have hm := (mod_iff_even s (16*t+10) q hq).2 (by omega)
  exact parent_arithmetic (16*t+10) q (by omega) hqmin hm

theorem parent_odd (s t q : Nat)
    (hq : 3^(16*t+14)*q+1 = 2^(2*(3*9^s))) (hqmin : 7 ≤ q) :
    ∃ v : Nat, 5 ≤ v ∧ v%2=1 ∧ 17*v+3=2^(16*t+15)*q := by
  have hm := (mod_iff_odd s (16*t+14) q hq).2 (by omega)
  exact parent_arithmetic (16*t+14) q (by omega) hqmin hm

#print axioms mod_iff_even
#print axioms mod_iff_odd
#print axioms parent_arithmetic
#print axioms parent_even
#print axioms parent_odd
end SheepA3Boost
