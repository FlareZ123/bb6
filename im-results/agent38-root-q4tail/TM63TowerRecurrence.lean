import Lean

/-!
A core-Lean formalization of the moving-exponent bounds used in the
TM63 published-tower sandwich. Indexing is shifted by one from the paper:
tower n is paper T_(n+1), with T_1 = 2; V starts at 63 and obeys
V_(j+1) = 2^V_j - 1.

The theorem below is a statement about this recurrence only. It does not
establish that the source machine follows the recurrence or halts.
-/

namespace TM63TowerRecurrence

/-- Paper tower T_(n+1) when T_1 = 2. -/
def tower : Nat → Nat
  | 0 => 2
  | n+1 => 2 ^ tower n

theorem tower_succ (n : Nat) : tower (n+1) = 2 ^ tower n := by rfl

/-- The recurrence sequence V_0 = 63, V_(j+1) = 2^V_j - 1.
    Irreducibility prevents elaboration from trying to normalize V_2 as an
    astronomically large numeral; V_succ exposes the exact recurrence. -/
def V : Nat → Nat := Nat.rec 63 (fun _ v => 2 ^ v - 1)
attribute [irreducible] V

/-- Exact integer encoding of T_(j+2)^(23/8) for j ≥ 2. -/
def lowerExp (j : Nat) : Nat := 2 ^ (23 * (tower j / 8))
/-- Exact integer encoding of T_(j+2)^4092. -/
def upperExp (j : Nat) : Nat := 2 ^ (4092 * tower j)

theorem four_le_tower_succ (n : Nat) : 4 ≤ tower (n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp [tower]
      calc
        4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ tower (n+1) := Nat.pow_le_pow_right (by decide) (by omega)

theorem sixteen_le_tower_of_two_le (n : Nat) (hn : 2 ≤ n) :
    16 ≤ tower n := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      simp [tower]
      calc
        16 = 2 ^ 4 := by decide
        _ ≤ 2 ^ tower (k+1) := Nat.pow_le_pow_right (by decide)
          (four_le_tower_succ k)

theorem eight_dvd_tower (n : Nat) (hn : 2 ≤ n) : 8 ∣ tower n := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      have h4 : 4 ≤ tower (k+1) := four_le_tower_succ k
      refine ⟨2 ^ (tower (k+1) - 3), ?_⟩
      calc
        2 ^ tower (k+1) = 2 ^ (3 + (tower (k+1) - 3)) := by
          congr 1
          omega
        _ = 2 ^ 3 * 2 ^ (tower (k+1) - 3) := by rw [Nat.pow_add]
        _ = 8 * 2 ^ (tower (k+1) - 3) := by rw [show 2 ^ 3 = 8 by decide]

theorem pow2_sub_one_gt (a b : Nat) (h : a + 2 ≤ b) :
    2 ^ a < 2 ^ b - 1 := by
  have hpow : 2 ^ (a+2) ≤ 2 ^ b :=
    Nat.pow_le_pow_right (by decide) h
  have hfactor : 2 ^ (a+2) = 4 * 2 ^ a := by
    rw [Nat.pow_add]
    simp [show 2 ^ 2 = 4 by decide, Nat.mul_comm]
  have hlarge : 4 * 2 ^ a ≤ 2 ^ b := by
    rw [← hfactor]
    exact hpow
  have hpos : 0 < 2 ^ a := Nat.pow_pos (by decide)
  omega

theorem two_le_tower (n : Nat) : 2 ≤ tower n := by
  cases n with
  | zero => decide
  | succ n => exact Nat.le_trans (by decide : 2 ≤ 4) (four_le_tower_succ n)

theorem lowerExp_ge_five (j : Nat) (hj : 2 ≤ j) : 5 ≤ lowerExp j := by
  have h16 := sixteen_le_tower_of_two_le j hj
  have hq : 2 ≤ tower j / 8 := by omega
  have he : 8 ≤ lowerExp j := by
    dsimp [lowerExp]
    calc
      8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ (23 * (tower j / 8)) :=
        Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem upperExp_ge_4093 (j : Nat) : 4093 ≤ upperExp j := by
  have h2 : 2 ≤ tower j := two_le_tower j
  have hexp : 13 ≤ 4092 * tower j := by omega
  calc
    4093 ≤ 2 ^ 13 := by decide
    _ ≤ 2 ^ (4092 * tower j) := Nat.pow_le_pow_right (by decide) hexp

theorem lowerExp_step_product_lt (j : Nat) (hj : 2 ≤ j) :
    tower (j+2) * lowerExp (j+1) < tower (j+2) ^ 4 := by
  let X := tower (j+2)
  let Y := tower (j+1)
  have hdiv : 8 ∣ Y := eight_dvd_tower (j+1) (by omega)
  have hquot : 8 * (Y / 8) = Y := Nat.mul_div_cancel' hdiv
  have hX : X = 2 ^ Y := by simp [X, Y, tower]
  have hprod : X * lowerExp (j+1) = 2 ^ (Y + 23 * (Y / 8)) := by
    calc
      X * lowerExp (j+1) = 2 ^ Y * 2 ^ (23 * (Y / 8)) := by
        change X * 2 ^ (23 * (tower (j+1) / 8)) = 2 ^ Y * 2 ^ (23 * (Y / 8))
        rw [hX]
      _ = 2 ^ (Y + 23 * (Y / 8)) := by rw [← Nat.pow_add]
  have hqpos : 0 < Y / 8 := by
    have h16 : 16 ≤ Y := sixteen_le_tower_of_two_le (j+1) (by omega)
    omega
  have hexp : Y + 23 * (Y / 8) < 4 * Y := by omega
  change X * lowerExp (j+1) < X ^ 4
  rw [hprod, hX]
  have hpow : 2 ^ (Y + 23 * (Y / 8)) < 2 ^ (4*Y) :=
    Nat.pow_lt_pow_right (by decide) hexp
  have hright : 2 ^ (4*Y) = (2 ^ Y) ^ 4 := by
    rw [show 4*Y = Y*4 by omega, Nat.pow_mul]
  rw [hright] at hpow
  exact hpow

theorem pow_five_gt_add_one (X : Nat) (hX : 2 ≤ X) :
    X ^ 4 + 1 ≤ X ^ 5 := by
  have hpos : 1 ≤ X ^ 4 := by
    have hp : 0 < X ^ 4 := Nat.pow_pos (by omega)
    omega
  have hmul : X ^ 4 * 2 ≤ X ^ 4 * X := Nat.mul_le_mul_left (X ^ 4) hX
  have hsmall : X ^ 4 + 1 ≤ X ^ 4 * 2 := by omega
  rw [Nat.pow_succ]
  exact Nat.le_trans hsmall hmul

theorem lowerExp_step_dominates (j : Nat) (hj : 2 ≤ j) :
    tower (j+2) ^ lowerExp j >
      tower (j+2) * lowerExp (j+1) + 1 := by
  let X := tower (j+2)
  have hX : 2 ≤ X := by
    change 2 ≤ tower (j+2)
    exact Nat.le_trans (by decide : 2 ≤ 4) (four_le_tower_succ (j+1))
  have he : 5 ≤ lowerExp j := lowerExp_ge_five j hj
  have hpow : X ^ 5 ≤ X ^ lowerExp j :=
    Nat.pow_le_pow_right (by omega) he
  have hprod : X * lowerExp (j+1) < X ^ 4 := by
    simpa [X] using lowerExp_step_product_lt j hj
  have hplus : X * lowerExp (j+1) + 1 ≤ X ^ 4 := by omega
  have h5 : X ^ 4 + 1 ≤ X ^ 5 := pow_five_gt_add_one X hX
  have hfinal : X * lowerExp (j+1) + 1 < X ^ 5 := by omega
  exact Nat.lt_of_lt_of_le hfinal hpow

theorem lowerExp_le (j : Nat) : 1 ≤ lowerExp j := by
  simp [lowerExp]
  exact Nat.one_le_pow _ 2 (by decide)

/-- The integer eighth root of T_(j+2) exists for every j ≥ 2. -/
theorem tower_succ_eq_eighth_root_pow (j : Nat) (hj : 2 ≤ j) :
    tower (j+1) = (2 ^ (tower j / 8)) ^ 8 := by
  have hdvd : 8 ∣ tower j := eight_dvd_tower j hj
  have hquot : 8 * (tower j / 8) = tower j := Nat.mul_div_cancel' hdvd
  rw [tower_succ, ← Nat.pow_mul]
  congr 1
  omega

theorem lowerExp_eq_eighth_root_pow (j : Nat) :
    lowerExp j = (2 ^ (tower j / 8)) ^ 23 := by
  simp [lowerExp, ← Nat.pow_mul, Nat.mul_comm]

theorem upperExp_eq_tower_pow (j : Nat) :
    upperExp j = tower (j+1) ^ 4092 := by
  calc
    upperExp j = 2 ^ (tower j * 4092) := by
      simp [upperExp, Nat.mul_comm]
    _ = (2 ^ tower j) ^ 4092 := by rw [Nat.pow_mul]
    _ = tower (j+1) ^ 4092 := by rfl

theorem tower0 : tower 0 = 2 := rfl
theorem tower1 : tower 1 = 4 := by decide
theorem tower2 : tower 2 = 16 := by decide
theorem tower3 : tower 3 = 65536 := by decide
theorem tower4 : tower 4 = 2 ^ 65536 := by simp [tower]
theorem V0 : V 0 = 63 := by unfold V; rfl
theorem V_succ (n : Nat) : V (n+1) = 2 ^ V n - 1 := by unfold V; rfl
theorem V1 : V 1 = 2 ^ 63 - 1 := by rw [V_succ, V0]
theorem V2 : V 2 = 2 ^ (V 1) - 1 := V_succ 1

theorem lowerExp2 : lowerExp 2 = 2 ^ 46 := by
  simp [lowerExp, tower]

theorem upperExp2 : upperExp 2 = 2 ^ 65472 := by
  simp [upperExp, tower]

theorem basePowerUpper (f : Nat) (hf : 0 < f)
    (hprod : V 1 * f < 2 ^ 65536) :
    V 2 ^ f < 2 ^ (2 ^ 65536) := by
  have hv : V 2 < 2 ^ V 1 := by
    rw [V2]
    exact Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hpow : V 2 ^ f < (2 ^ V 1) ^ f :=
    Nat.pow_lt_pow_left hv (Nat.ne_of_gt hf)
  have hpow' : (2 ^ V 1) ^ f = 2 ^ (V 1 * f) := by
    rw [Nat.pow_mul]
  rw [hpow'] at hpow
  have hfinal : 2 ^ (V 1 * f) < 2 ^ (2 ^ 65536) :=
    Nat.pow_lt_pow_right (by decide) hprod
  exact Nat.lt_trans hpow hfinal

theorem tower_recurrence_base :
    tower 4 ^ lowerExp 2 < V 2 ∧ V 2 ^ upperExp 2 < tower 5 := by
  have hlow : tower 4 ^ lowerExp 2 < V 2 := by
    rw [tower4, lowerExp2, V2]
    have hexp : 65536 * 2 ^ 46 = 2 ^ 62 := by
      rw [show 65536 = 2 ^ 16 by decide, ← Nat.pow_add]
    have hpow : (2 ^ 65536) ^ (2 ^ 46) = 2 ^ (2 ^ 62) := by
      rw [← Nat.pow_mul, hexp]
    rw [hpow]
    have hmargin : 2 ^ 62 + 2 ≤ V 1 := by
      rw [V1]
      decide
    exact pow2_sub_one_gt (2 ^ 62) (V 1) hmargin
  have hupp : V 2 ^ upperExp 2 < tower 5 := by
    rw [upperExp2, tower_succ, tower4]
    have hsmall : V 1 < 2 ^ 63 := by
      rw [V1]
      exact Nat.sub_lt (by decide) (by decide)
    have hmul : V 1 * 2 ^ 65472 < 2 ^ 63 * 2 ^ 65472 :=
      Nat.mul_lt_mul_of_pos_right hsmall (Nat.pow_pos (by decide))
    have hpowmul : 2 ^ 63 * 2 ^ 65472 = 2 ^ 65535 := by
      rw [← Nat.pow_add]
    have hexp : V 1 * 2 ^ 65472 < 2 ^ 65536 := by
      have hstep : 2 ^ 65535 < 2 ^ 65536 :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      rw [hpowmul] at hmul
      exact Nat.lt_trans hmul hstep
    exact basePowerUpper (2 ^ 65472) (Nat.pow_pos (by decide)) hexp
  exact ⟨hlow, hupp⟩

/-- One induction step for the coupled moving-exponent estimates. -/
theorem tower_recurrence_step (j : Nat) (hj : 2 ≤ j)
    (hLower : tower (j+2) ^ lowerExp j < V j)
    (hUpper : V j ^ upperExp j < tower (j+3)) :
    tower (j+3) ^ lowerExp (j+1) < V (j+1) ∧
      V (j+1) ^ upperExp (j+1) < tower (j+4) := by
  let X := tower (j+2)
  have hX : 2 ≤ X := by
    change 2 ≤ tower (j+2)
    exact Nat.le_trans (by decide : 2 ≤ 4) (four_le_tower_succ (j+1))
  have hLowerDominates := lowerExp_step_dominates j hj
  have hLowerMargin : X * lowerExp (j+1) + 2 ≤ V j := by
    have h1 : X ^ lowerExp j < V j := by simpa [X] using hLower
    have h2 : X * lowerExp (j+1) + 1 < X ^ lowerExp j := by
      simpa [X] using hLowerDominates
    omega
  have hLowerPow := pow2_sub_one_gt
    (X * lowerExp (j+1)) (V j) hLowerMargin
  have hLowerNext : tower (j+3) ^ lowerExp (j+1) < V (j+1) := by
    calc
      tower (j+3) ^ lowerExp (j+1) =
          (2 ^ X) ^ lowerExp (j+1) := by simp [X, tower]
      _ = 2 ^ (X * lowerExp (j+1)) := by rw [Nat.pow_mul]
      _ < 2 ^ (V j) - 1 := hLowerPow
      _ = V (j+1) := by rw [V_succ]

  have hXltV : X < V j := by
    have hExpOne : 1 ≤ lowerExp j := lowerExp_le j
    have hPowLe : X ≤ X ^ lowerExp j := by
      calc
        X = X ^ 1 := by simp
        _ ≤ X ^ lowerExp j := Nat.pow_le_pow_right (by omega) hExpOne
    exact Nat.lt_of_le_of_lt hPowLe (by simpa [X] using hLower)
  have hf : 4093 ≤ upperExp j := upperExp_ge_4093 j
  have hfmargin : 4092 ≤ upperExp j - 1 := by omega
  have hpow4092 : X ^ 4092 < V j ^ 4092 :=
    Nat.pow_lt_pow_left hXltV (by decide)
  have hpowrest : V j ^ 4092 ≤ V j ^ (upperExp j - 1) :=
    Nat.pow_le_pow_right (by omega) hfmargin
  have hpowProd : X ^ 4092 < V j ^ (upperExp j - 1) :=
    Nat.lt_of_lt_of_le hpow4092 hpowrest
  have hVpos : 0 < V j := by omega
  have hprod : X ^ 4092 * V j < V j ^ upperExp j := by
    have hmul := Nat.mul_lt_mul_of_pos_right hpowProd hVpos
    have hfpos : 1 ≤ upperExp j := by omega
    calc
      X ^ 4092 * V j < V j ^ (upperExp j - 1) * V j := hmul
      _ = V j ^ (upperExp j - 1 + 1) := by rw [Nat.pow_succ]
      _ = V j ^ upperExp j := by rw [Nat.sub_add_cancel hfpos]
  have hUpperProd : X ^ 4092 * V j < tower (j+3) :=
    Nat.lt_trans hprod hUpper
  have hVnext : V (j+1) < 2 ^ V j := by
    rw [V_succ]
    exact Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hVnextPow : V (j+1) ^ (X ^ 4092) < (2 ^ V j) ^ (X ^ 4092) :=
    Nat.pow_lt_pow_left hVnext (Nat.ne_of_gt (Nat.pow_pos (by omega)))
  have hpowMul : (2 ^ V j) ^ (X ^ 4092) = 2 ^ (V j * X ^ 4092) := by
    rw [Nat.pow_mul]
  have hcomm : V j * X ^ 4092 = X ^ 4092 * V j := Nat.mul_comm _ _
  have hUpperNext : V (j+1) ^ upperExp (j+1) < tower (j+4) := by
    rw [upperExp_eq_tower_pow (j+1)]
    calc
      V (j+1) ^ (tower (j+2) ^ 4092) =
          V (j+1) ^ (X ^ 4092) := by simp [X]
      _ < 2 ^ (V j * X ^ 4092) := by rw [← hpowMul]; exact hVnextPow
      _ < 2 ^ tower (j+3) := by
        rw [hcomm]
        exact Nat.pow_lt_pow_right (by decide) hUpperProd
      _ = tower (j+4) := by rfl
  exact ⟨hLowerNext, hUpperNext⟩

/-- For paper indexing, T_(j+3)^(T_(j+2)^(23/8)) < V_j and
    V_j^(T_(j+2)^4092) < T_(j+4), for every j ≥ 2. This is the
    recurrence-only tower sandwich; machine execution is a separate premise. -/
theorem tower_recurrence_bounds (j : Nat) (hj : 2 ≤ j) :
    tower (j+2) ^ lowerExp j < V j ∧
      V j ^ upperExp j < tower (j+3) := by
  have hall : ∀ k, tower (k+4) ^ lowerExp (k+2) < V (k+2) ∧
      V (k+2) ^ upperExp (k+2) < tower (k+5) := by
    intro k
    induction k with
    | zero =>
        simpa only [Nat.zero_add] using tower_recurrence_base
    | succ k ih =>
        have hprev : 2 ≤ k+2 := by omega
        exact tower_recurrence_step (k+2) hprev ih.1 ih.2
  have hEq : j = (j-2)+2 := by omega
  rw [hEq]
  simpa [Nat.add_assoc] using hall (j-2)

#print axioms tower_recurrence_bounds
#print axioms tower_recurrence_step

end TM63TowerRecurrence
