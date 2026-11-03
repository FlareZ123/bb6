import Std
namespace BB6.Agent17Forward

private theorem le_pow_two (k : Nat) : k ≤ 2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    have hpos : 0 < (2:Nat)^k := Nat.pow_pos (by decide)
    omega

/-- A true generic-branch first-even return from a source divisible by 2^k
    can attain any prescribed even residue s modulo 2^k. -/
theorem zero_two_power_generic (k s : Nat) (_hk : 1 ≤ k) (hs : s%2=0) :
    let b := 2^k
    let u := 1+2*s+4*2^k
    0 < b ∧ 5 ≤ u ∧ u%4=1 ∧
      (4^b*u)%(2^k)=0 ∧
      ((4^b*u + 2*b + (u-1)/2)%(2^k))=s%(2^k) := by
  dsimp
  let q:=2^k
  let b:=q
  let u:=1+2*s+4*q
  have hq : 0<q := Nat.pow_pos (by decide)
  have hkbound : k ≤ q := le_pow_two k
  have hdiv4 : q ∣ 4^b := by
    have hbase : (2:Nat)^k ∣ (2:Nat)^b := Nat.pow_dvd_pow 2 hkbound
    have hm : (4:Nat)^b = (2:Nat)^b * 2^b := by
      rw [show (4:Nat)=2*2 by decide,Nat.mul_pow]
    rw [hm]
    exact Nat.dvd_mul_right_of_dvd hbase (2^b)
  have hx : q ∣ 4^b*u := Nat.dvd_mul_right_of_dvd hdiv4 u
  have hx0 : (4^b*u)%q=0 := Nat.mod_eq_zero_of_dvd hx
  have hb0 : (2*b)%q=0 := by
    apply Nat.mod_eq_zero_of_dvd
    change q ∣ 2*q
    exact Nat.dvd_mul_left q 2
  have h2q : (2*q)%q=0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left q 2)
  have half : (u-1)/2=s+2*q := by
    dsimp [u]
    omega
  have hu : u%4=1 := by
    dsimp [u]
    omega
  refine ⟨hq, ?_, hu, hx0, ?_⟩
  · omega
  · change (4^b*u+2*b+(u-1)/2)%q=s%q
    rw [half]
    simp [Nat.add_mod,hx0,hb0,h2q]

#print axioms zero_two_power_generic
end BB6.Agent17Forward
