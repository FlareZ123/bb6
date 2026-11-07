import Lean
import Lean.Elab.Tactic.Omega

namespace S4WeightFormula

def W : List Nat → Nat
  | [] => 0
  | b :: T => b + 1 + 2 * W T

def H (a : Nat) (L : List Nat) : Option (List Nat) :=
  match L with
  | [] =>
      if a % 2 = 0 then
        if a = 0 then none else some [a / 2 + 2, a / 2 - 1]
      else
        if a ≤ 1 then none else (H (a / 2) []).map (a / 2 :: ·)
  | b :: S =>
      if a % 2 = 0 then some ((a / 2 + 2) :: (b + a / 2) :: S)
      else (H (b + a / 2 + 1) S).map (a / 2 :: ·)
termination_by (L.length, a)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | apply Prod.Lex.left; simp | apply Prod.Lex.right; omega

def v2 (n : Nat) : Nat :=
  if n = 0 then 0 else if n % 2 = 0 then v2 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

def M : Nat → List Nat → Nat
  | _, [] => 0
  | 0, b :: S => b + 1 + 2 * W S
  | j + 1, b :: S => b + 1 + 2 * (M j S + W S)

theorem M_nil (j : Nat) : M j [] = 0 := by
  cases j <;> rfl

def Mfull : List Nat → Nat
  | [] => 0
  | b :: S => b + 1 + 2 * (Mfull S + W S)

theorem M_ge_len : ∀ (j : Nat) (L : List Nat), L.length ≤ j → M j L = Mfull L := by
  intro j
  induction j with
  | zero =>
      intro L h
      cases L <;> simp [M, Mfull] at h ⊢
  | succ j ih =>
      intro L h
      cases L with
      | nil => rfl
      | cons b S =>
          have hS : S.length ≤ j := by simp at h; omega
          simp [M, Mfull, ih S hS]

theorem v2_even {n : Nat} (hn : n ≠ 0) (he : n % 2 = 0) :
    v2 n = v2 (n / 2) + 1 := by
  rw [v2]
  simp [hn, he]

theorem v2_odd {n : Nat} (he : n % 2 = 1) : v2 n = 0 := by
  have hn : n ≠ 0 := by omega
  have hne : n % 2 ≠ 0 := by omega
  rw [v2]
  simp [hn, hne]

theorem v2_two_mul {n : Nat} (hn : n ≠ 0) : v2 (2 * n) = v2 n + 1 := by
  have he : (2 * n) % 2 = 0 := by omega
  have hdiv : (2 * n) / 2 = n := by omega
  rw [v2_even (by omega) he, hdiv]

theorem algebra_add (j x z : Nat) :
    2 * x + 2 * ((j + 3) * x + z) = (j + 4) * (2 * x) + 2 * z := by
  calc
    2 * x + 2 * ((j + 3) * x + z)
        = 2 * x + (2 * ((j + 3) * x) + 2 * z) := by rw [Nat.mul_add]
    _ = (2 * x + 2 * ((j + 3) * x)) + 2 * z := by omega
    _ = (j + 4) * (2 * x) + 2 * z := by
      rw [← mul_succ_add]
      rfl
where
  mul_succ_add (j x : Nat) : (j + 4) * (2 * x) = 2 * x + 2 * ((j + 3) * x) := by
    calc
      (j + 4) * (2 * x) = ((j + 4) * 2) * x := by rw [Nat.mul_assoc]
      _ = (2 * (j + 4)) * x := by rw [Nat.mul_comm (j + 4) 2]
      _ = 2 * ((j + 4) * x) := by rw [Nat.mul_assoc]
      _ = 2 * (((j + 3) + 1) * x) := by rfl
      _ = 2 * ((j + 3) * x + x) := by rw [Nat.add_mul]; simp
      _ = 2 * ((j + 3) * x) + 2 * x := by rw [Nat.mul_add]
      _ = 2 * x + 2 * ((j + 3) * x) := by omega

set_option maxHeartbeats 0 in
theorem H_weight_formula : ∀ (L : List Nat) (a : Nat) (U : List Nat),
    H a L = some U →
    2 * W U + 2 * M (v2 (a + 1 + 2 * W L)) L =
      (v2 (a + 1 + 2 * W L) + 3) * (a + 1 + 2 * W L)
        + 3 * 2 ^ (v2 (a + 1 + 2 * W L)) := by
  intro L
  induction L with
  | nil =>
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
          intro U h
          by_cases he : a % 2 = 0
          · by_cases hz : a = 0
            · simp [H, he, hz] at h
            · simp [H, he, hz] at h
              subst U
              simp [W] at *
              have hv : v2 (a + 1) = 0 := v2_odd (by omega)
              rw [hv, M_nil]
              omega
          · by_cases hs : a ≤ 1
            · simp [H, he, hs] at h
            · have hsmall : a / 2 < a := by omega
              have hpow : a + 1 = 2 * (a / 2 + 1) := by omega
              have hpos : a / 2 + 1 ≠ 0 := by omega
              cases hH : H (a / 2) [] with
              | none => simp [H, he, hs, hH] at h
              | some V =>
                  have hV : H (a / 2) [] = some V := hH
                  have hEq : U = (a / 2) :: V := by
                    simp [H, he, hs, hH] at h
                    exact h.symm
                  have hIH := ih (a / 2) hsmall V hV
                  subst U
                  have hIH' : 2 * W V =
                      (v2 (a / 2 + 1) + 3) * (a / 2 + 1) + 3 * 2 ^ (v2 (a / 2 + 1)) := by
                    simpa [W, M_nil] using hIH
                  simp only [W] at hIH' ⊢
                  rw [M_nil]
                  rw [hpow, v2_two_mul hpos]
                  simp only [Nat.pow_succ]
                  calc
                    2 * (a / 2 + 1 + 2 * W V)
                        = 2 * (a / 2 + 1) + 2 * (2 * W V) := by omega
                    _ = 2 * (a / 2 + 1) +
                        2 * ((v2 (a / 2 + 1) + 3) * (a / 2 + 1) +
                          3 * 2 ^ (v2 (a / 2 + 1))) := by rw [hIH']
                    _ = (v2 (a / 2 + 1) + 4) * (2 * (a / 2 + 1)) +
                        3 * (2 ^ (v2 (a / 2 + 1)) * 2) := by
                          simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                            (algebra_add (v2 (a / 2 + 1)) (a / 2 + 1)
                              (3 * 2 ^ (v2 (a / 2 + 1)))
  | cons b S ih =>
      intro a U h
      by_cases he : a % 2 = 0
      · simp [H, he] at h
        subst U
        have hXodd : (a + 1 + 2 * W (b :: S)) % 2 = 1 := by simp [W]; omega
        have hv : v2 (a + 1 + 2 * W (b :: S)) = 0 := v2_odd hXodd
        rw [hv]
        simp [W, M]
        omega
      · have ha : a = 2 * (a / 2) + 1 := by omega
        let a' := b + a / 2 + 1
        let X' := a' + 1 + 2 * W S
        have hX : a + 1 + 2 * W (b :: S) = 2 * X' := by
          simp [W, X', a']
          omega
        have hXpos : X' ≠ 0 := by simp [X', a']
        cases hH : H a' S with
        | none => simp [H, he, a', hH] at h
        | some V =>
            have hV : H a' S = some V := hH
            have hEq : U = (a / 2) :: V := by
              simp [H, he, a', hH] at h
              exact h.symm
            have hIH := ih a' V hV
            subst U
            have hIH' : 2 * W V + 2 * M (v2 X') S =
                (v2 X' + 3) * X' + 3 * 2 ^ (v2 X') := by
              simpa [X'] using hIH
            have hL : 2 * W (a / 2 :: V) + 2 * M (v2 X' + 1) (b :: S) =
                2 * X' + 2 * (2 * W V + 2 * M (v2 X') S) := by
              simp [W, M, X', a']
              omega
            rw [hX, v2_two_mul hXpos]
            simp [Nat.pow_succ]
            calc
              2 * W (a / 2 :: V) + 2 * M (v2 X' + 1) (b :: S)
                  = 2 * X' + 2 * (2 * W V + 2 * M (v2 X') S) := hL
              _ = 2 * X' + 2 * ((v2 X' + 3) * X' + 3 * 2 ^ (v2 X')) := by rw [hIH']
              _ = (v2 X' + 4) * (2 * X') + 3 * 2 ^ (v2 X' + 1) := by
                simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                  (algebra_add (v2 X') X' (3 * 2 ^ (v2 X')))

theorem H_weight_formula_ge_len (L : List Nat) (a : Nat) (U : List Nat)
    (h : H a L = some U)
    (hLen : L.length ≤ v2 (a + 1 + 2 * W L)) :
    2 * W U + 2 * Mfull L =
      (v2 (a + 1 + 2 * W L) + 3) * (a + 1 + 2 * W L)
        + 3 * 2 ^ (v2 (a + 1 + 2 * W L)) := by
  have hm := M_ge_len (v2 (a + 1 + 2 * W L)) L hLen
  rw [← hm]
  exact H_weight_formula L a U h

#print axioms H_weight_formula
#print axioms H_weight_formula_ge_len
end S4WeightFormula
