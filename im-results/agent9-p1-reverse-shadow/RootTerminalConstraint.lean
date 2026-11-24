import ReverseUnitMap

namespace BB6P1Unit

/-- Exact predecessor forced by a rooted terminal unit. If the moving
    modulus is Q=q+m and the final remainder is 1, the preceding remainder
    is necessarily (Q+1)/2; in particular the final unit bit is one. -/
theorem root_terminal_predecessor (q d m : Nat)
    (hd : d < q) (hm : 0 < m)
    (hroot : run q d m = 1) :
    2 * run q d (m-1) = q+m+1 ∧
      bit (q+m-1) (run q d (m-1)) = 1 := by
  let x := run q d (m-1)
  have hstep : run q d m =
      unit (q+(m-1)) (run q d (m-1)) := by
    cases m with
    | zero => omega
    | succ k => simp [run]
  have hmod : (2*x)%(q+m) = 1 := by
    rw [hstep, unit] at hroot
    have hidx : q+(m-1)+1 = q+m := by omega
    simpa [x, hidx] using hroot
  have hxlt : x < q+(m-1) := by
    dsimp [x]
    exact run_lt q d (m-1) hd
  have hbound : 2*x < 2*(q+m) := by omega
  have hdouble : 2*x = q+m+1 := by
    by_cases hlt : 2*x < q+m
    · rw [Nat.mod_eq_of_lt hlt] at hmod
      omega
    · have hge : q+m ≤ 2*x := by omega
      have hsub : 2*x-(q+m) < q+m := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub] at hmod
      omega
  have hidx : q+m-1+1 = q+m := by omega
  have hbit : bit (q+m-1) x = 1 := by
    simp [bit, hidx, hdouble]
  exact ⟨hdouble, by simpa [x] using hbit⟩

#print axioms root_terminal_predecessor

end BB6P1Unit
