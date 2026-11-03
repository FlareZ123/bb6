import Row262

namespace BB6.Row262

/-- Exact positive first A-return: no earlier positive time is in state A. -/
def FirstAReturn (ls : List Bool) (h : Bool) (rs : List Bool) (n : Nat) : Prop :=
  0 < n ∧ (run n ⟨0, ls, h, rs⟩).st = 0 ∧
  ∀ m : Nat, 0 < m → m < n → (run m ⟨0, ls, h, rs⟩).st ≠ 0

/-- Closure of a predicate that sees only the scanned bit and the right tape,
    for all first A-returns, quantified over arbitrary forgotten left tapes. -/
def FirstRightOnlyClosed (P : Bool → List Bool → Prop) : Prop :=
  ∀ (ls : List Bool) (h : Bool) (rs : List Bool) (n : Nat),
    P h rs → FirstAReturn ls h rs n →
    P (run n ⟨0, ls, h, rs⟩).head (run n ⟨0, ls, h, rs⟩).right

private theorem first_segment_1 : FirstAReturn [] false [] 2 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 := by omega
  rcases hcases with h <;> subst m <;> decide

private theorem first_segment_2 : FirstAReturn [true,true,true,false,true] true [true] 7 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hcases with h | h | h | h | h | h <;> subst m <;> decide

private theorem first_segment_3 : FirstAReturn [true,false,false] true [true,false,false,false,false,true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hcases with h | h | h | h <;> subst m <;> decide

private theorem first_segment_4 : FirstAReturn [] false [true,false,false,true,false,false,false,false,true] 6 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hcases with h | h | h | h | h <;> subst m <;> decide

private theorem first_segment_5 : FirstAReturn [] false [true,false,false,false,false,false,true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hcases with h | h | h | h <;> subst m <;> decide

private theorem first_segment_6 : FirstAReturn [] false [false,true] 2 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 := by omega
  rcases hcases with h <;> subst m <;> decide

private theorem first_segment_7 : FirstAReturn [true,true,true,false,false] true [true,true] 7 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hcases with h | h | h | h | h | h <;> subst m <;> decide

private theorem first_segment_8 : FirstAReturn [] false [true,false,false,false,false,true,true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hpos hbound
  have hcases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hcases with h | h | h | h <;> subst m <;> decide

/-- An eight-edge abstract path, each edge a source-valid first A-return.
    The left tape is independently chosen on each edge; this is not a
    reachable blank-tape halting computation. -/
theorem first_right_only_closure_forces_halt_guard
    (P : Bool → List Bool → Prop)
    (hblank : P false [])
    (hclosed : FirstRightOnlyClosed P) :
    P false [true, true] := by
  have h1 : P true [true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [] false [] 2 hblank first_segment_1)
  have h2 : P true [true,false,false,false,false,true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [true,true,true,false,true] true [true] 7 h1 first_segment_2)
  have h3 : P false [true,false,false,true,false,false,false,false,true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [true,false,false] true [true,false,false,false,false,true] 5 h2 first_segment_3)
  have h4 : P false [true,false,false,false,false,false,true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [] false [true,false,false,true,false,false,false,false,true] 6 h3 first_segment_4)
  have h5 : P false [false,true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [] false [true,false,false,false,false,false,true] 5 h4 first_segment_5)
  have h6 : P true [true,true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [] false [false,true] 2 h5 first_segment_6)
  have h7 : P false [true,false,false,false,false,true,true] := by
    simpa [run, step, moveL, moveR] using
      (hclosed [true,true,true,false,false] true [true,true] 7 h6 first_segment_7)
  simpa [run, step, moveL, moveR] using
    (hclosed [] false [true,false,false,false,false,true,true] 5 h7 first_segment_8)

/-- No right-only first-return-closed predicate can both contain the
    blank projection and forbid every A0/right11 halting guard. -/
theorem no_safe_first_right_only_closed
    (P : Bool → List Bool → Prop)
    (hblank : P false [])
    (hclosed : FirstRightOnlyClosed P)
    (hsafe : ∀ rs : List Bool, ¬ P false (true :: true :: rs)) : False := by
  exact hsafe [] (first_right_only_closure_forces_halt_guard P hblank hclosed)

end BB6.Row262

#print axioms BB6.Row262.first_right_only_closure_forces_halt_guard
#print axioms BB6.Row262.no_safe_first_right_only_closed
