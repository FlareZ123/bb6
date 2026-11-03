import PairBurst
set_option maxHeartbeats 1000000
namespace BB6.Row262

-- Finite nonnegative 2-adic valuation. Zero is assigned valuation zero.
def v2 (n : Nat) : Nat :=
  if h0 : n = 0 then 0
  else if heven : n % 2 = 0 then 1 + v2 (n/2)
  else 0
termination_by n
decreasing_by omega

theorem v2_twice (n : Nat) (hn : n > 0) : v2 (2*n) = v2 n + 1 := by
  have hpos : 2*n ≠ 0 := by omega
  have hmod : 2*n % 2 = 0 := by omega
  rw [v2]
  simp [hpos, hmod]
  omega

theorem v2_pos_even (n : Nat) (hn : n > 0) (hv : v2 n > 0) : n % 2 = 0 := by
  by_cases he : n % 2 = 0
  · exact he
  · have hf : v2 n = 0 := by
      rw [v2]
      simp [Nat.ne_of_gt hn, he]
    omega

theorem v2_at_least_three_div8 (n : Nat) (hn : n > 0) (hv : v2 n ≥ 3) : n % 8 = 0 := by
  have h0 : n % 2 = 0 := v2_pos_even n hn (by omega)
  let a := n / 2
  have na : n = 2 * a := by dsimp [a]; omega
  have ha : a > 0 := by omega
  have ha_val : v2 a ≥ 2 := by
    have h := v2_twice a ha
    rw [na, h] at hv
    omega
  have h1 : a % 2 = 0 := v2_pos_even a ha (by omega)
  let b := a / 2
  have ab : a = 2*b := by dsimp [b]; omega
  have hb : b > 0 := by omega
  have hb_val : v2 b ≥ 1 := by
    have h := v2_twice b hb
    rw [ab, h] at ha_val
    omega
  have h2 : b % 2 = 0 := v2_pos_even b hb (by omega)
  omega

theorem v2_tail_lt_three (y : Nat) (h : y % 8 ≠ 4) : v2 (4+7*y) < 3 := by
  have hp : 4+7*y > 0 := by omega
  have hm : (4+7*y) % 8 ≠ 0 := by omega
  by_cases hv : v2 (4+7*y) < 3
  · exact hv
  · have hc := v2_at_least_three_div8 (4+7*y) hp (by omega)
    exact False.elim (hm hc)

theorem v2_times8 (n : Nat) (hn : n > 0) : v2 (8*n) = v2 n + 3 := by
  have h2 : 2*n > 0 := by omega
  have h4 : 2*(2*n) > 0 := by omega
  have ht : 8*n=2*(2*(2*n)) := by omega
  rw [ht, v2_twice (2*(2*n)) h4, v2_twice (2*n) h2, v2_twice n hn]

-- Number of initial base-eight digit-4 blocks, i.e. tape triples 001.
def prefix8 (y : Nat) : Nat :=
  if h : y % 8 = 4 then 1 + prefix8 (y/8) else 0
termination_by y
decreasing_by omega

theorem valuation_burst (y : Nat) :
    3 * prefix8 y ≤ v2 (4 + 7*y) ∧
    v2 (4 + 7*y) < 3 * prefix8 y + 3 := by
  induction y using Nat.strongRecOn with
  | ind y ih =>
      by_cases hh : y % 8 = 4
      · have hlt : y/8 < y := by omega
        have heq : y = 8 * (y/8) + 4 := by omega
        have hnum : 4+7*y=8*(4+7*(y/8)) := by omega
        have htail : 4+7*(y/8)>0 := by omega
        have hind := ih (y/8) hlt
        have hv : v2 (4+7*y) = v2 (4+7*(y/8))+3 := by
          rw [hnum,v2_times8 _ htail]
        have hp : prefix8 y = 1+prefix8 (y/8) := by rw [prefix8]; simp [hh]
        rw [hp,hv]
        omega
      · have hval := v2_tail_lt_three y hh
        have hp : prefix8 y = 0 := by rw [prefix8]; simp [hh]
        rw [hp]
        omega

theorem valuation_right_prefix (y : Nat) :
    (v2 (7*(1+4*y)+9)-2)/3 = prefix8 y := by
  have h : 7*(1+4*y)+9 = 2*(2*(4+7*y)) := by omega
  have hp : 4+7*y>0 := by omega
  have h2 : 2*(4+7*y)>0 := by omega
  have hv : v2 (7*(1+4*y)+9) = v2 (4+7*y) + 2 := by
    rw [h,v2_twice (2*(4+7*y)) h2,v2_twice (4+7*y) hp]
  have hb := valuation_burst y
  omega

-- Nearest-first right-tape bit list as a little-endian natural number.
def bitsVal : List Bool → Nat
  | [] => 0
  | b :: ys => (if b then 1 else 0) + 2*bitsVal ys

theorem bits_001 (ys : List Bool) :
    bitsVal (false::false::true::ys) = 4+8*bitsVal ys := by simp [bitsVal]; omega

theorem prefix8_001 (ys : List Bool) :
    prefix8 (bitsVal (false::false::true::ys)) = 1 + prefix8 (bitsVal ys) := by
  rw [bits_001, prefix8]
  have hmod : (4+8*bitsVal ys)%8=4 := by omega
  simp only [hmod, dite_true]
  have hdiv : (4+8*bitsVal ys)/8=bitsVal ys := by omega
  rw [hdiv]

theorem right_burst_count (q : Nat) (ys : List Bool) :
    prefix8 (bitsVal (rightBurst q ++ ys)) = q + prefix8 (bitsVal ys) := by
  induction q generalizing ys with
  | zero => simp [rightBurst]
  | succ q ih =>
      have hlist : rightBurst (q+1) ++ ys =
          rightBurst q ++ (false::false::true::ys) := by
        simp [rightBurst, List.append_assoc]
      rw [hlist, ih, prefix8_001]
      omega

-- With a maximal 001 prefix, the full original right-tape integer R
-- yields its length q by floor((v2(7R+9)-2)/3).
theorem right_burst_maximal_valuation (q : Nat) (ys : List Bool)
    (hmax : bitsVal ys % 8 ≠ 4) :
    (v2 (7*bitsVal ([true,false] ++ rightBurst q ++ ys)+9)-2)/3 = q := by
  have hbits : bitsVal ([true,false] ++ rightBurst q ++ ys) =
      1+4*bitsVal (rightBurst q ++ ys) := by simp [bitsVal]; omega
  rw [hbits, valuation_right_prefix, right_burst_count]
  have hrest : prefix8 (bitsVal ys) = 0 := by
    rw [prefix8]
    simp [hmax]
  omega

#print axioms BB6.Row262.valuation_burst
#print axioms BB6.Row262.valuation_right_prefix
#print axioms BB6.Row262.right_burst_count
#print axioms BB6.Row262.right_burst_maximal_valuation
end BB6.Row262
