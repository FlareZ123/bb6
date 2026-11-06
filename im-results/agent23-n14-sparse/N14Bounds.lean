import Lean
namespace Agent23N14

theorem large_pow_succ (k : Nat) :
    256*(k+15) ≤ 2^(k+14) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have he : k+1+14=k+14+1 := by omega
    rw [he, Nat.pow_succ]
    omega

theorem large_pow (n : Nat) (hn : 14≤n) :
    256*(n+1)≤2^n := by
  have h := large_pow_succ (n-14)
  have he : n-14+14=n := by omega
  simpa only [he, show n-14+15=n+1 by omega] using h

theorem pow_scale (m : Nat) (hm : m≤8) : 2^m ≤ 256 := by
  have he : 2^m ≤ (2:Nat)^8 := Nat.pow_le_pow_right (by decide) hm
  simpa only [show (2:Nat)^8=256 by decide] using he

theorem wall_impossible
    (n b0 b m : Nat) (hn : 14≤n) (hm : m≤8)
    (hroot : b0+2*n+16=14*2^n)
    (hleft : b0+12≤2^m*(b+12)) : 4*(n+m)<b := by
  by_cases hle : b≤4*(n+m)
  ·
    have hupper : b+12 ≤ 4*n+44 := by omega
    have hpow := pow_scale m hm
    have hcross : 2^m*(b+12) ≤ 256*(4*n+44) := by
      calc
        2^m*(b+12) ≤ 2^m*(4*n+44) := Nat.mul_le_mul_left _ hupper
        _ ≤ 256*(4*n+44) := Nat.mul_le_mul_right _ hpow
    have hgrowth := large_pow n hn
    have hgrowth14 : 14*(256*(n+1))≤14*2^n := Nat.mul_le_mul_left _ hgrowth
    omega
  · omega

theorem big_cost_impossible
    (n m : Nat) (hn : 14≤n) (hm : m≤8) :
    ¬14*2^n≤6*m+14*n+10 := by
  intro h
  have hp := large_pow n hn
  have hmul := Nat.mul_le_mul_left 14 hp
  omega

#print axioms wall_impossible
#print axioms big_cost_impossible
end Agent23N14
