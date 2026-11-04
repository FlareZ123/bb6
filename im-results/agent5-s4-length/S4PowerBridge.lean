import S4PowerGate
import S4Length
import Lean.Elab.Tactic.Omega
namespace S4Power

theorem W_eq_source (T : List Nat) : W T = S4Length.W T := by
  induction T with
  | nil => rfl
  | cons b S ih => simp [W,S4Length.W,ih]

theorem H_eq_source : ∀ (L : List Nat) (a : Nat), H a L = S4Length.H a L := by
  intro L
  induction L with
  | nil =>
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
        by_cases he : a % 2 = 0
        · simp [H, S4Length.H, he]
        · by_cases hz : a ≤ 1
          · simp [H, S4Length.H, he, hz]
          · have hlt : a/2 < a := by omega
            have hh := ih (a/2) hlt
            rw [H, S4Length.H]
            simp only [he, hz, ite_false]
            exact congrArg (fun z : Option (List Nat) => z.map (a/2::·)) hh
  | cons b S ih =>
      intro a
      by_cases he : a % 2 = 0
      · simp [H, S4Length.H, he]
      · have hh := ih (b+a/2+1)
        simp [H, S4Length.H, he, hh]

theorem F_eq_source (T : List Nat) : F T = S4Length.F T := by
  have hb : bump17 = S4Length.bump17 := by
    funext T
    cases T <;> rfl
  cases T with
  | nil => simp [F,S4Length.F,H_eq_source,hb]
  | cons b S => simp [F,S4Length.F,H_eq_source,hb]

theorem source_F_none_iff_pow2 (T : List Nat) :
    S4Length.F T = none ↔ Pow2 (S4Length.W T+45) := by
  rw [←F_eq_source,←W_eq_source]
  exact F_none_iff_pow2 T

#print axioms source_F_none_iff_pow2
end S4Power
