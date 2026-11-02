import Std
namespace SheepEvenNew

/-- The modular period on odd m lifts to modulus 2m for all positive powers. -/
theorem pow_mod_period (m p r k : Nat) (hm : 1 < m)
    (hp : 2^p % m = 1) :
    2^(r+p*k) % m = 2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m, hp]
  simp [Nat.mod_eq_of_lt hm]

theorem pow_mod_twice_period (m p r k : Nat) (hm : 1 < m)
    (hp : 2^p % m = 1) (hr : 0 < r) :
    2^(r+p*k) % (2*m) = 2^r % (2*m) := by
  have heq := pow_mod_period m p (r-1) k hm hp
  have hleft : 2^(r+p*k) % (2*m) = 2*(2^(r-1+p*k)%m) := by
    have h : r+p*k=(r-1+p*k)+1 := by omega
    rw [h, Nat.pow_succ]
    rw [show 2*m=m*2 by omega, Nat.mul_mod_mul_right]
    omega
  have hright : 2^r % (2*m) = 2*(2^(r-1)%m) := by
    have hpowsucc : 2^r = 2^(r-1)*2 := by
      calc
        2^r = 2^((r-1)+1) := by congr 1; omega
        _ = 2^(r-1)*2 := by rw [Nat.pow_succ]
    rw [hpowsucc]
    rw [show 2*m=m*2 by omega, Nat.mul_mod_mul_right]
    omega
  rw [hleft, hright, heq]

/-- Handles an arbitrary signed affine offset rather than only natural offsets. -/
theorem signed_affine_period (d M n k : Nat) (B : Int)
    (hd : 1 < d) (hn : 0 < n) (hper : 2^M % d = 1) :
    (((2^(n+M*k) : Nat) : Int) + B) % ((2*d : Nat) : Int) =
    (((2^n : Nat) : Int) + B) % ((2*d : Nat) : Int) := by
  have hmod := pow_mod_twice_period d M n k hd hper hn
  have hh : (((2^(n+M*k) : Nat) : Int) % ((2*d : Nat) : Int)) =
      (((2^n : Nat) : Int) % ((2*d : Nat) : Int)) := by
    rw [←Int.natCast_emod, ←Int.natCast_emod]
    exact congrArg Int.ofNat hmod
  calc
    (((2^(n+M*k) : Nat) : Int) + B) % ((2*d : Nat) : Int)
        = (((2^(n+M*k) : Nat) : Int) % ((2*d : Nat) : Int) + B % ((2*d : Nat) : Int)) % ((2*d : Nat) : Int) := by
          rw [Int.add_emod]
    _ = (((2^n : Nat) : Int) % ((2*d : Nat) : Int) + B % ((2*d : Nat) : Int)) % ((2*d : Nat) : Int) := by rw [hh]
    _ = (((2^n : Nat) : Int) + B) % ((2*d : Nat) : Int) := by exact (Int.add_emod ((2^n : Nat) : Int) B ((2*d : Nat) : Int)).symm

/-- The precise odd-quotient filter for the Sheep generic inverse equation. -/
theorem odd_quotient_residue (d v : Nat) (_hd : 0 < d) (hv : v % 2 = 1) :
    (d*v)%(2*d)=d := by
  rw [show 2*d = d*2 by omega, Nat.mul_mod_mul_left]
  rw [hv]
  omega

/-- A periodic negative-offset exclusion remains excluded for all k. -/
theorem exclude_signed_pair (d M n : Nat) (B : Int)
    (hd : 1 < d) (hn : 0 < n) (hper : 2^M % d = 1)
    (hbase : (((2^n : Nat) : Int)+B) % ((2*d : Nat) : Int) ≠ (d : Int))
    (k : Nat) :
    (((2^(n+M*k) : Nat) : Int)+B) % ((2*d : Nat) : Int) ≠ (d : Int) := by
  rw [signed_affine_period d M n k B hd hn hper]
  exact hbase

#print axioms signed_affine_period
#print axioms odd_quotient_residue
#print axioms exclude_signed_pair
end SheepEvenNew
