import BMod7Cycle
namespace BB6.OneDim

/-- The final scalar iterate may be written as a final G call. -/
theorem iterG_succ_right (n z : Nat) : iterG (n+1) z = G (iterG n z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      change iterG (n+1) (G z) = G (iterG (n+1) z)
      exact ih (G z)

theorem G_no_two_mod3 (z : Nat) : G z % 3 ≠ 2 := by
  simp only [G]
  omega

theorem iterG_pos_no_two_mod3 (n z : Nat) (hn : 0<n) :
    iterG n z %3 ≠ 2 := by
  have h : n=(n-1)+1 := by omega
  rw [h, iterG_succ_right]
  exact G_no_two_mod3 _

theorem scalarA_odd (n : Nat) : scalarA n %2=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      let z := iterG (scalarA n) 0
      have hb : z%2=0 ∨ z%2=1 := by omega
      rcases hb with hz | hz
      · change (z+9-3*(z%2))%2=1
        rw [hz]
        omega
      · change (z+9-3*(z%2))%2=1
        rw [hz]
        omega

theorem scalarA_positive (n : Nat) : 0<scalarA n := by
  induction n with
  | zero => decide
  | succ n ih =>
      let z := iterG (scalarA n) 0
      have hb : z%2≤1 := by omega
      simp only [scalarA]
      omega

end BB6.OneDim
