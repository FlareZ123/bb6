import S4WeightedDrift
import S4Length

namespace S4Length

theorem H_eq_original : ∀ (L : List Nat) (a : Nat),
    S4Length.H a L = _root_.H a L := by
  intro L
  induction L with
  | nil =>
      intro a
      induction a using Nat.strongRecOn with
      | ind a ih =>
        by_cases he : a % 2 = 0
        · simp [S4Length.H, _root_.H, he]
        · by_cases hz : a ≤ 1
          · simp [S4Length.H, _root_.H, he, hz]
          · have hlt : a/2 < a := by omega
            have hh := ih (a/2) hlt
            rw [S4Length.H, _root_.H]
            simp only [he, hz, ite_false]
            exact congrArg (fun z : Option (List Nat) => z.map (a/2::·)) hh
  | cons b S ih =>
      intro a
      by_cases he : a % 2 = 0
      · simp [S4Length.H, _root_.H, he]
      · have hh := ih (b+a/2+1)
        simp [S4Length.H, _root_.H, he, hh]

theorem bump17_eq_original (T : List Nat) :
    S4Length.bump17 T = _root_.bump17 T := by
  cases T <;> rfl

theorem W_eq_original (T : List Nat) :
    S4Length.W T = _root_.W T := by
  induction T with
  | nil => rfl
  | cons b S ih => simp [S4Length.W, _root_.W, ih]

theorem F_eq_original (T : List Nat) :
    S4Length.F T = _root_.compactNext T := by
  have heq : S4Length.bump17 = _root_.bump17 := funext bump17_eq_original
  cases T with
  | nil =>
      simp [S4Length.F, _root_.compactNext, _root_.compactInitial,
        H_eq_original, heq]
  | cons b S =>
      simp [S4Length.F, _root_.compactNext, _root_.compactInitial,
        H_eq_original, heq]

theorem source_compact_length (T U : List Nat)
    (hs : _root_.compactNext T = some U)
    (k t : Nat) (hf : _root_.W T + 45 = 2^k * (2*t+1)) :
    U.length = max T.length (k+2) := by
  have h : S4Length.F T = some U := (F_eq_original T).trans hs
  exact F_length T U h k t (by simpa [W_eq_original] using hf)

#print axioms source_compact_length
#print axioms H_eq_original
end S4Length
