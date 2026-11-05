import LastResetStrengthSource

namespace BB6.Agent43CountedEnergy

open BB6.Agent28 BB6.Agent1Quarter BB6.Agent1UpperTail BB6.Agent47P1
open BB6.Agent43LastResetStrength

private theorem n_le_two_pow (n : Nat) : n ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have hp : 0 < (2:Nat)^n := Nat.pow_pos (by decide)
    omega

/-- Every original positive-depth P1 inverse step has a uniformly bounded
    rescaled left coordinate, with no affine-wall assumption. -/
theorem source_positive_reset_energy_factor
    (n bp dp mp t k c : Nat) (hn : 14 ≤ n)
    (hpre : OddCone (14*2^n-2*n-16) 3 bp dp mp)
    (hb : 8 ≤ bp) (hb4 : bp%4=0) (hd : dp%2=1)
    (hi : inverseAt bp dp t=some (k,c))
    (hk : 2 ≤ k) (hc : c%2=1) (ht : 1 ≤ t) :
    2^(t+1)*((2*k-4)+12) ≤
      (8*2^n*2^n)*(bp+12) := by
  have hnP : n ≤ 2^n := n_le_two_pow n
  have hroot : (14*2^n-2*n-16)+2*n+16=14*2^n := by omega
  have hmassPre := odd_cone_mass (14*2^n-2*n-16) 3 bp dp mp hpre
  have hpow := (inverseAt_iff_power_mass bp dp t k c
    (by omega) hb4 hd).mp hi
  have hc4 : 4 ≤ c+3 := by omega
  have hpLower : (2^t)*4 ≤ (2^t)*(c+3) :=
    Nat.mul_le_mul_left (2^t) hc4
  have hpBound : 2^(t+1) ≤ 8*2^n := by
    rw [Nat.pow_succ]
    omega
  have hpost : OddCone (14*2^n-2*n-16) 3
      (2*k-4) (c+4) (mp+t+1) :=
    OddCone.parent bp dp mp t k c hpre hb hb4 hd hi hk hc
  have hmassPost := odd_cone_mass
    (14*2^n-2*n-16) 3
    (2*k-4) (c+4) (mp+t+1) hpost
  have hout : (2*k-4)+12 ≤ 14*2^n := by omega
  have hmul : 2^(t+1)*((2*k-4)+12) ≤
      (8*2^n)*(14*2^n) :=
    Nat.mul_le_mul hpBound hout
  have hcoeff : 112 ≤ 8*(bp+12) := by omega
  have hcoeffmul : 112*(2^n*2^n) ≤
      (8*(bp+12))*(2^n*2^n) :=
    Nat.mul_le_mul_right (2^n*2^n) hcoeff
  calc
    2^(t+1)*((2*k-4)+12) ≤ (8*2^n)*(14*2^n) := hmul
    _ = (8*14)*(2^n*2^n) := by ac_rfl
    _ = 112*(2^n*2^n) := by simp
    _ ≤ (8*(bp+12))*(2^n*2^n) := hcoeffmul
    _ = (8*2^n*2^n)*(bp+12) := by ac_rfl

/-- A single original critical CountCone of arbitrary finite length obeys
    a uniform energy envelope in its exact true reset count z. -/
theorem source_counted_energy_bound
    (n b d m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    2^m*(b+12) ≤ (16*2^n)*(8*2^n*2^n)^z := by
  induction h with
  | root =>
    have hP : n ≤ 2^n := n_le_two_pow n
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one]
    omega
  | parent bp dp mp zp t k c hp hb hb4 hd hi hk hc ih =>
    by_cases ht : t=0
    · have hz0 : zp + (if t=0 then 0 else 1)=zp := by simp [ht]
      have hhalve := (inv0_halve bp dp k c (by simpa [ht] using hi) hk).1
      have hE : 2^(mp+t+1)*((2*k-4)+12)=
          2^mp*(bp+12) := by
        rw [ht, Nat.add_zero, Nat.pow_succ]
        calc
          (2^mp*2)*((2*k-4)+12) =
            2^mp*(2*((2*k-4)+12)) := by ac_rfl
          _ = 2^mp*(bp+12) := by rw [hhalve]
      rw [hz0, hE]
      exact ih
    · have htpos : 1 ≤ t := by omega
      have hpreOdd : OddCone (14*2^n-2*n-16) 3 bp dp mp :=
        counted_to_odd_cone _ _ _ _ _ _ hp
      have hfactor := source_positive_reset_energy_factor n bp dp mp t k c
        hn hpreOdd hb hb4 hd hi hk hc htpos
      have hnewBound : 2^(mp+t+1)*((2*k-4)+12) ≤
          (8*2^n*2^n)*(2^mp*(bp+12)) := by
        calc
          2^(mp+t+1)*((2*k-4)+12) =
            2^mp*(2^(t+1)*((2*k-4)+12)) := by
              have hh : mp+t+1=mp+(t+1) := by omega
              rw [hh, Nat.pow_add]
              ac_rfl
          _ ≤ 2^mp*((8*2^n*2^n)*(bp+12)) :=
            Nat.mul_le_mul_left (2^mp) hfactor
          _ = (8*2^n*2^n)*(2^mp*(bp+12)) := by ac_rfl
      have hmul : (8*2^n*2^n)*(2^mp*(bp+12)) ≤
          (8*2^n*2^n)*((16*2^n)*(8*2^n*2^n)^zp) :=
        Nat.mul_le_mul_left (8*2^n*2^n) ih
      have hfinal : 2^(mp+t+1)*((2*k-4)+12) ≤
          (16*2^n)*(8*2^n*2^n)^(zp+1) := by
        calc
          _ ≤ (8*2^n*2^n)*(2^mp*(bp+12)) := hnewBound
          _ ≤ (8*2^n*2^n)*((16*2^n)*(8*2^n*2^n)^zp) := hmul
          _ = (16*2^n)*(8*2^n*2^n)^(zp+1) := by
            rw [Nat.pow_succ]
            ac_rfl
      simpa only [if_neg ht] using hfinal

#print axioms BB6.Agent43CountedEnergy.source_positive_reset_energy_factor
#print axioms BB6.Agent43CountedEnergy.source_counted_energy_bound

end BB6.Agent43CountedEnergy
