import Row262
set_option maxHeartbeats 500000

namespace BB6.Row262

theorem replicate_false_shift (k : Nat) (rs : List Bool) :
    List.replicate k false ++ false :: rs = false :: List.replicate k false ++ rs := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate, ih]

theorem e_blank_sweep (k : Nat) (rs : List Bool) :
    run (k+2) ⟨4, List.replicate k true, true, rs⟩ =
      ⟨0, [], false, true :: List.replicate (k+1) false ++ rs⟩ := by
  induction k generalizing rs with
  | zero => rfl
  | succ k ih =>
      calc
        run (k+3) ⟨4, List.replicate (k+1) true, true, rs⟩
            = run (k+2) ⟨4, List.replicate k true, true, false :: rs⟩ := by
              simp [run, step, moveL, List.replicate]
        _ = ⟨0, [], false, true :: List.replicate (k+1) false ++ false :: rs⟩ := ih (false :: rs)
        _ = ⟨0, [], false, true :: List.replicate (k+2) false ++ rs⟩ := by
              simp [List.replicate, replicate_false_shift]

theorem a_one_all_ones (k : Nat) (rs : List Bool) :
    run (k+4) ⟨0, List.replicate k true, true, rs⟩ =
      ⟨0, [], false, true :: List.replicate (k+1) false ++ rs⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
      have h := run_add 3 (k+2) ⟨0, List.replicate (k+1) true, true, rs⟩
      have h' : 3+(k+2)=k+5 := by omega
      rw [h'] at h
      rw [h, a_one_front]
      simpa [List.replicate, replicate_false_shift] using (e_blank_sweep k (false :: rs))

theorem e_explicit_last_zero (k : Nat) (rs : List Bool) :
    run (k+2) ⟨4, List.replicate k true ++ [false], true, rs⟩ =
      ⟨0, [], false, true :: List.replicate (k+1) false ++ rs⟩ := by
  induction k generalizing rs with
  | zero => rfl
  | succ k ih =>
      calc
        run (k+3) ⟨4, List.replicate (k+1) true ++ [false], true, rs⟩
            = run (k+2) ⟨4, List.replicate k true ++ [false], true, false :: rs⟩ := by
              simp [run, step, moveL, List.replicate]
        _ = ⟨0, [], false, true :: List.replicate (k+1) false ++ false :: rs⟩ := ih (false :: rs)
        _ = ⟨0, [], false, true :: List.replicate (k+2) false ++ rs⟩ := by
              simp [List.replicate, replicate_false_shift]

theorem a_one_explicit_last_zero (k : Nat) (rs : List Bool) :
    run (k+4) ⟨0, List.replicate k true ++ [false], true, rs⟩ =
      ⟨0, [], false, true :: List.replicate (k+1) false ++ rs⟩ := by
  cases k with
  | zero => rfl
  | succ k =>
      have h := run_add 3 (k+2) ⟨0, List.replicate (k+1) true ++ [false], true, rs⟩
      have h' : 3+(k+2)=k+5 := by omega
      rw [h'] at h
      rw [h, a_one_front]
      simpa [List.replicate, replicate_false_shift] using (e_explicit_last_zero k (false :: rs))

theorem left_shape (ls : List Bool) :
    (∃ k, ls = List.replicate k true) ∨
    (∃ k, ls = List.replicate k true ++ [false]) ∨
    (∃ k x ys, ls = List.replicate k true ++ false :: x :: ys) := by
  induction ls with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons b ys ih =>
      cases b with
      | false =>
          cases ys with
          | nil => exact Or.inr (Or.inl ⟨0, rfl⟩)
          | cons x xs => exact Or.inr (Or.inr ⟨0, x, xs, rfl⟩)
      | true =>
          rcases ih with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, x, xs, hk⟩
          · exact Or.inl ⟨k+1, by simp [hk, List.replicate]⟩
          · exact Or.inr (Or.inl ⟨k+1, by simp [hk, List.replicate]⟩)
          · exact Or.inr (Or.inr ⟨k+1, x, xs, by simp [hk, List.replicate]⟩)

theorem a_one_returns_within (left rs : List Bool) :
    ∃ n, 4 ≤ n ∧ n ≤ left.length + 4 ∧
      (run n ⟨0, left, true, rs⟩).st = 0 := by
  rcases left_shape left with ⟨k,hk⟩ | ⟨k,hk⟩ | ⟨k,x,ys,hk⟩
  · refine ⟨k+4, by omega, ?_, ?_⟩
    · simp [hk]
    · simp [hk, a_one_all_ones]
  · refine ⟨k+4, by omega, ?_, ?_⟩
    · simp [hk]
    · simp [hk, a_one_explicit_last_zero]
  · refine ⟨k+4, by omega, ?_, ?_⟩
    · simp [hk]
    · simp [hk, a_one_sweep]

theorem a_zero_returns_or_halting_gate (left right : List Bool) :
    ∃ n, 2 ≤ n ∧ n ≤ 7 ∧
      ((run n ⟨0,left,false,right⟩).st = 0 ∨
       ((run n ⟨0,left,false,right⟩).st = 5 ∧
        (run n ⟨0,left,false,right⟩).head = true)) := by
  cases right with
  | nil =>
      exact ⟨2, by omega, by omega, Or.inl (by rfl)⟩
  | cons b rs =>
      cases b with
      | false =>
          exact ⟨2, by omega, by omega, Or.inl (by rfl)⟩
      | true =>
          cases rs with
          | nil =>
              exact ⟨5, by omega, by omega, Or.inl (by rfl)⟩
          | cons b2 rs2 =>
              cases b2 with
              | true =>
                  exact ⟨2, by omega, by omega, Or.inr ⟨by rfl, by rfl⟩⟩
              | false =>
                  cases rs2 with
                  | nil =>
                      exact ⟨5, by omega, by omega, Or.inl (by rfl)⟩
                  | cons b3 rs3 =>
                      cases rs3 with
                      | nil =>
                          exact ⟨5, by omega, by omega, Or.inl (by cases b3 <;> rfl)⟩
                      | cons b4 rs4 =>
                          cases b4 with
                          | false =>
                              exact ⟨5, by omega, by omega, Or.inl (by cases b3 <;> rfl)⟩
                          | true =>
                              cases b3 with
                              | false =>
                                  exact ⟨6, by omega, by omega, Or.inl (by simp only [a_zero_d_one_c_zero])⟩
                              | true =>
                                  exact ⟨7, by omega, by omega, Or.inl (by simp only [a_zero_d_one_c_one])⟩

theorem any_A_return_or_halt (left right : List Bool) (read : Bool) :
    ∃ n, 2 ≤ n ∧ n ≤ left.length + 7 ∧
      ((run n ⟨0,left,read,right⟩).st = 0 ∨
       ((run n ⟨0,left,read,right⟩).st = 5 ∧
        (run n ⟨0,left,read,right⟩).head = true)) := by
  cases read with
  | false =>
      obtain ⟨n, lower, upper, dest⟩ := a_zero_returns_or_halting_gate left right
      exact ⟨n, lower, by omega, dest⟩
  | true =>
      obtain ⟨n, lower, upper, dest⟩ := a_one_returns_within left right
      exact ⟨n, by omega, by omega, Or.inl dest⟩


theorem a_zero_halt_two_iff (left right : List Bool) :
    ((run 2 ⟨0,left,false,right⟩).st = 5 ∧
     (run 2 ⟨0,left,false,right⟩).head = true) ↔
      right.headD false = true ∧ right.tail.headD false = true := by
  cases right with
  | nil => simp [run, step, moveR, moveL]
  | cons b rest =>
      cases b with
      | false => simp [run, step, moveR, moveL]
      | true =>
          cases rest with
          | nil => simp [run, step, moveR, moveL]
          | cons b2 tail => cases b2 <;> simp [run, step, moveR, moveL]

end BB6.Row262
#print axioms BB6.Row262.a_one_all_ones
#print axioms BB6.Row262.a_one_explicit_last_zero
#print axioms BB6.Row262.any_A_return_or_halt
#print axioms BB6.Row262.a_zero_halt_two_iff
