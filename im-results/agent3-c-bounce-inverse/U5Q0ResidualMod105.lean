import U5Q0M16Residual
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

namespace BB6.Agent3U5Q0ResidualMod105

open BB6.Agent3U5M16Residual

private theorem pow4_mod3 (r : Nat) : 4 ^ r % 3 = 1 := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
      norm_num

private theorem pow2_mod3_of_odd (n : Nat) (hn : n % 2 = 1) : 2 ^ n % 3 = 2 := by
  have hdecomp : n = 2 * (n / 2) + 1 := by omega
  rw [hdecomp, Nat.pow_succ, Nat.pow_mul]
  rw [show (2 : Nat) ^ 2 = 4 by norm_num, Nat.mul_mod, pow4_mod3]
  norm_num

/-- The authentic U5 residual identity plus t=39+64h forces h=0 mod 3. -/
theorem residual_h_mod3 (w s m t h : Nat)
    (hs : 211 * s + 129 = 5 * 2 ^ (201 + 3360 * w))
    (hm : 32 * s = 32 + 840 * w + m)
    (hp : m + 1 = 8 * t + 1)
    (ht : t = 39 + 64 * h) : h % 3 = 0 := by
  have hid := u5_m8_t_identity w s m t hs hm hp
  have hE : 201 + 3360 * w = 2 * (100 + 1680 * w) + 1 := by omega
  have hpow : 2 ^ (201 + 3360 * w) % 3 = 2 := by
    rw [hE]
    exact pow2_mod3_of_odd _ (by omega)
  have hleft : (211 * t + 1360 + 22155 * w) % 3 = (t + 1) % 3 := by omega
  have hright : (20 * 2 ^ (201 + 3360 * w)) % 3 = 1 := by
    rw [Nat.mul_mod, hpow]
    norm_num
  have hmod := congrArg (fun z : Nat => z % 3) hid
  rw [hleft, hright] at hmod
  have htmod : t % 3 = 0 := by omega
  rw [ht] at htmod
  omega

/-- The q parameter in every secondary bounce parent satisfies q=2 mod 3. -/
theorem bounce_q_mod3 (h r q : Nat)
    (hh : h % 3 = 0)
    (hfan : 4 ^ r * q = 416 + 684 * h) : q % 3 = 2 := by
  have hpow := pow4_mod3 r
  have hleft : (4 ^ r * q) % 3 = q % 3 := by
    rw [Nat.mul_mod, hpow]
    norm_num
  have hright : (416 + 684 * h) % 3 = 2 := by omega
  have hmod := congrArg (fun z : Nat => z % 3) hfan
  rw [hleft, hright] at hmod
  exact hmod

/-- Every B_(r,h) target has x+y=0 mod 3. -/
theorem bounce_target_sum_mod3 (h r q x y : Nat)
    (hh : h % 3 = 0)
    (hfan : 4 ^ r * q = 416 + 684 * h)
    (hx : x + 2 = 2 * q)
    (hy : y + q + 3 * r = 2487 + 4096 * h) : (x + y) % 3 = 0 := by
  have hq := bounce_q_mod3 h r q hh hfan
  have hsum : x + y + 3 * r = 2485 + 4096 * h + q := by omega
  have hleft : (x + y + 3 * r) % 3 = (x + y) % 3 := by omega
  have hright : (2485 + 4096 * h + q) % 3 = 0 := by omega
  have hmod := congrArg (fun z : Nat => z % 3) hsum
  rw [hleft, hright] at hmod
  exact hmod

/-- The B_(r,h) right coordinate is uniformly large for r>=1. -/
theorem bounce_target_y_ge_1135 (h r q y : Nat)
    (hr : 1 <= r)
    (hfan : 4 ^ r * q = 416 + 684 * h)
    (hy : y + q + 3 * r = 2487 + 4096 * h) : 1135 <= y := by
  have hqpos : 1 <= q := by
    by_contra hn
    have hqzero : q = 0 := by omega
    rw [hqzero] at hfan
    omega
  have h4 : 4 <= 4 ^ r := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := by omega
    rw [Nat.pow_succ]
    have hpos : 1 <= 4 ^ r' := by positivity
    omega
  have hqmul : 4 * q <= 4 ^ r * q := Nat.mul_le_mul_right q h4
  rw [hfan] at hqmul
  have hqbound : q <= 104 + 171 * h := by omega
  have hrpow : ∀ n : Nat, n <= 4 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Nat.pow_succ]
        have hpos : 1 <= 4 ^ n := by positivity
        omega
  have hrmul : 4 ^ r <= 4 ^ r * q := Nat.mul_le_mul_left (4 ^ r) hqpos
  rw [hfan] at hrmul
  have hrbound : r <= 416 + 684 * h := le_trans (hrpow r) hrmul
  omega

/-- The exact a=0 source branch cannot produce a secondary bounce target. -/
theorem no_zero_left_bounce_parent (h r q x y k n : Nat)
    (hh : h % 3 = 0)
    (hfan : 4 ^ r * q = 416 + 684 * h)
    (hx : x + 2 = 2 * q)
    (hy : y + q + 3 * r = 2487 + 4096 * h)
    (hparent : x + y = 8 * 2 ^ n)
    (hcost : 2 * k + 9 + 3 * n = x + 2 * y) : False := by
  have hsum := bounce_target_sum_mod3 h r q x y hh hfan hx hy
  have hn : n % 2 = 1 := by omega
  have hpow := pow2_mod3_of_odd n hn
  have hright : (8 * 2 ^ n) % 3 = 1 := by
    rw [Nat.mul_mod, hpow]
    norm_num
  have hmod := congrArg (fun z : Nat => z % 3) hparent
  rw [hsum, hright] at hmod
  omega

/-- The exact a=1 source branch cannot produce a secondary bounce target. -/
theorem no_one_left_bounce_parent (h r q x y k n : Nat)
    (hh : h % 3 = 0)
    (hfan : 4 ^ r * q = 416 + 684 * h)
    (hx : x + 2 = 2 * q)
    (hy : y + q + 3 * r = 2487 + 4096 * h)
    (hparent : x + y + 1 = 16 * 2 ^ n)
    (hcost : 2 * k + 11 + 3 * n = x + 2 * y) : False := by
  have hsum := bounce_target_sum_mod3 h r q x y hh hfan hx hy
  have hn : n % 2 = 1 := by omega
  have hpow := pow2_mod3_of_odd n hn
  have hleft : (x + y + 1) % 3 = 1 := by omega
  have hright : (16 * 2 ^ n) % 3 = 2 := by
    rw [Nat.mul_mod, hpow]
    norm_num
  have hmod := congrArg (fun z : Nat => z % 3) hparent
  rw [hleft, hright] at hmod
  omega


private theorem pow8_mod7 (n : Nat) : 8 ^ n % 7 = 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih]
      norm_num

private theorem pow2_mod7_of_three_multiple (n k : Nat)
    (hn : n = 3 * k) : 2 ^ n % 7 = 1 := by
  rw [hn, Nat.pow_mul, show (2 : Nat) ^ 3 = 8 by norm_num]
  exact pow8_mod7 k

/-- The residual identity forces h=4 mod 5 on t=39+64h. -/
theorem residual_h_mod5 (w s m t h : Nat)
    (hs : 211 * s + 129 = 5 * 2 ^ (201 + 3360 * w))
    (hm : 32 * s = 32 + 840 * w + m)
    (hp : m + 1 = 8 * t + 1)
    (ht : t = 39 + 64 * h) : h % 5 = 4 := by
  have hid := u5_m8_t_identity w s m t hs hm hp
  have hleft : (211 * t + 1360 + 22155 * w) % 5 = t % 5 := by omega
  have hright : (20 * 2 ^ (201 + 3360 * w)) % 5 = 0 := by omega
  have hmod := congrArg (fun z : Nat => z % 5) hid
  rw [hleft, hright] at hmod
  have htmod : t % 5 = 0 := by omega
  rw [ht] at htmod
  omega

/-- The residual identity forces h=0 mod 7 on t=39+64h. -/
theorem residual_h_mod7 (w s m t h : Nat)
    (hs : 211 * s + 129 = 5 * 2 ^ (201 + 3360 * w))
    (hm : 32 * s = 32 + 840 * w + m)
    (hp : m + 1 = 8 * t + 1)
    (ht : t = 39 + 64 * h) : h % 7 = 0 := by
  have hid := u5_m8_t_identity w s m t hs hm hp
  have hE : 201 + 3360 * w = 3 * (67 + 1120 * w) := by omega
  have hpow : 2 ^ (201 + 3360 * w) % 7 = 1 := by
    exact pow2_mod7_of_three_multiple _ _ hE
  have hleft : (211 * t + 1360 + 22155 * w) % 7 = (t + 2) % 7 := by omega
  have hright : (20 * 2 ^ (201 + 3360 * w)) % 7 = 6 := by
    rw [Nat.mul_mod, hpow]
    norm_num
  have hmod := congrArg (fun z : Nat => z % 7) hid
  rw [hleft, hright] at hmod
  have htmod : t % 7 = 4 := by omega
  rw [ht] at htmod
  omega

/-- The complete residual branch fixes h modulo 105. -/
theorem residual_h_mod105 (w s m t h : Nat)
    (hs : 211 * s + 129 = 5 * 2 ^ (201 + 3360 * w))
    (hm : 32 * s = 32 + 840 * w + m)
    (hp : m + 1 = 8 * t + 1)
    (ht : t = 39 + 64 * h) : h % 105 = 84 := by
  have h3 := residual_h_mod3 w s m t h hs hm hp ht
  have h5 := residual_h_mod5 w s m t h hs hm hp ht
  have h7 := residual_h_mod7 w s m t h hs hm hp ht
  omega

/-- The secondary-fan quotient S=416+684h is 17 mod 105. -/
theorem secondary_S_mod105 (h : Nat) (hh : h % 105 = 84) :
    (416 + 684 * h) % 105 = 17 := by omega
end BB6.Agent3U5Q0ResidualMod105
