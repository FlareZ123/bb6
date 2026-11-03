import Row262

namespace BB6.Row262.Window

open BB6.Row262

/-- Normalize a right tape by removing physically irrelevant trailing zeros. -/
def trimRight : List Bool → List Bool
  | [] => []
  | b :: bs =>
    let tail := trimRight bs
    if b == false && tail.isEmpty then [] else b :: tail

/-- First k tape symbols to the left, nearest-first; missing cells are blank. -/
def windowLeft (k : Nat) (ls : List Bool) : List Bool :=
  (ls ++ List.replicate k false).take k

/-- A positive first return to state A on a literal complete finite tape. -/
def FirstAReturn (ls : List Bool) (h : Bool) (rs : List Bool) (n : Nat) : Prop :=
  0 < n ∧ (run n ⟨0, ls, h, rs⟩).st = 0 ∧
  ∀ m : Nat, 0 < m → m < n → (run m ⟨0, ls, h, rs⟩).st ≠ 0

/-- All-left-context first-return closure for a proposed k-bit left-window
    invariant that also reads the scanned bit and full right tape. -/
def FirstWindowClosed (k : Nat) (P : List Bool → Bool → List Bool → Prop) : Prop :=
  ∀ (ls : List Bool) (h : Bool) (rs : List Bool) (n : Nat),
    P (windowLeft k ls) h (trimRight rs) → FirstAReturn ls h rs n →
    P (windowLeft k (run n ⟨0, ls, h, rs⟩).left)
      (run n ⟨0, ls, h, rs⟩).head
      (trimRight (run n ⟨0, ls, h, rs⟩).right)

private theorem first_segment_1 :
    FirstAReturn [false, false, false, false] false [] 2 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 := by omega
  rcases hc with a <;> subst m <;> decide

private theorem first_segment_2 :
    FirstAReturn [false, false, false, false, false, false] true [true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_3 :
    FirstAReturn [false, false, false, false] false [true, false, true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hc with a | a | a | a <;> subst m <;> decide

private theorem first_segment_4 :
    FirstAReturn [false, true, false, true] false [] 2 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 := by omega
  rcases hc with a <;> subst m <;> decide

private theorem first_segment_5 :
    FirstAReturn [false, true, false, true, true, true] true [true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_6 :
    FirstAReturn [false, true, true, true, false, true] true [true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_7 :
    FirstAReturn [true, true, false, true, false, false, false, false] true [true, false, true, false, true] 6 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hc with a | a | a | a | a <;> subst m <;> decide

private theorem first_segment_8 :
    FirstAReturn [false, false, false, false, false, false] true [true, false, false, false, true, false, true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_9 :
    FirstAReturn [false, false, false, false] false [true, false, true, false, false, false, true, false, true, false, true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hc with a | a | a | a <;> subst m <;> decide

private theorem first_segment_10 :
    FirstAReturn [false, true, false, true] false [false, true, false, true, false, true] 2 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 := by omega
  rcases hc with a <;> subst m <;> decide

private theorem first_segment_11 :
    FirstAReturn [false, true, false, true, false, false] true [true, true, false, true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_12 :
    FirstAReturn [false, true, false, false, false, false] true [true, false, true, true, false, true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_13 :
    FirstAReturn [false, false, false, false, false, false] true [true, false, true, false, true, true, false, true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_14 :
    FirstAReturn [false, false, false, false] false [true, false, true, false, true, false, true, true, false, true, false, true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hc with a | a | a | a <;> subst m <;> decide

private theorem first_segment_15 :
    FirstAReturn [false, true, false, true, true, true] true [false, true, true, false, true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_16 :
    FirstAReturn [false, true, true, true, true, false] true [true, false, false, true, true, false, true, false, true] 4 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hc with a | a | a <;> subst m <;> decide

private theorem first_segment_17 :
    FirstAReturn [true, true, true, false, false, false, false, false, false] true [true, false, true, false, false, true, true, false, true, false, true] 7 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
  rcases hc with a | a | a | a | a | a <;> subst m <;> decide

private theorem first_segment_18 :
    FirstAReturn [false, false, false, false] false [true, false, false, false, false, true, false, true, false, false, true, true, false, true, false, true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hc with a | a | a | a <;> subst m <;> decide

private theorem first_segment_19 :
    FirstAReturn [false, false, false, true] false [true, false, true, false, false, true, true, false, true, false, true] 5 := by
  refine ⟨by omega, by decide, ?_⟩
  intro m hm hmn
  have hc : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hc with a | a | a | a <;> subst m <;> decide

/-- Any four-left-bit window predicate containing blank and closed under
    arbitrary left extensions has a specific A0/right11 halting projection.
    The 19 source-exact first returns use independently selected tails. -/
theorem left_four_window_forces_halt_guard
    (P : List Bool → Bool → List Bool → Prop)
    (hblank : P [false,false,false,false] false [])
    (hclosed : FirstWindowClosed 4 P) :
    P [false, true, false, true] false [true, true, false, true, false, true] := by
  have h1 : P [false, false, false, false] true [true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false] false [] 2 hblank first_segment_1)
  have h2 : P [false, false, false, false] false [true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false, false, false] true [true] 4 h1 first_segment_2)
  have h3 : P [false, true, false, true] false [] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false] false [true, false, true] 5 h2 first_segment_3)
  have h4 : P [false, true, false, true] true [true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, false, true] false [] 2 h3 first_segment_4)
  have h5 : P [false, true, true, true] true [true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, false, true, true, true] true [true] 4 h4 first_segment_5)
  have h6 : P [true, true, false, true] true [true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, true, true, false, true] true [true, false, true] 4 h5 first_segment_6)
  have h7 : P [false, false, false, false] true [true, false, false, false, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [true, true, false, true, false, false, false, false] true [true, false, true, false, true] 6 h6 first_segment_7)
  have h8 : P [false, false, false, false] false [true, false, true, false, false, false, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false, false, false] true [true, false, false, false, true, false, true, false, true] 4 h7 first_segment_8)
  have h9 : P [false, true, false, true] false [false, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false] false [true, false, true, false, false, false, true, false, true, false, true] 5 h8 first_segment_9)
  have h10 : P [false, true, false, true] true [true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, false, true] false [false, true, false, true, false, true] 2 h9 first_segment_10)
  have h11 : P [false, true, false, false] true [true, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, false, true, false, false] true [true, true, false, true, false, true] 4 h10 first_segment_11)
  have h12 : P [false, false, false, false] true [true, false, true, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, false, false, false, false] true [true, false, true, true, false, true, false, true] 4 h11 first_segment_12)
  have h13 : P [false, false, false, false] false [true, false, true, false, true, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false, false, false] true [true, false, true, false, true, true, false, true, false, true] 4 h12 first_segment_13)
  have h14 : P [false, true, false, true] true [false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false] false [true, false, true, false, true, false, true, true, false, true, false, true] 5 h13 first_segment_14)
  have h15 : P [false, true, true, true] true [true, false, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, false, true, true, true] true [false, true, true, false, true, false, true] 4 h14 first_segment_15)
  have h16 : P [true, true, true, false] true [true, false, true, false, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, true, true, true, true, false] true [true, false, false, true, true, false, true, false, true] 4 h15 first_segment_16)
  have h17 : P [false, false, false, false] false [true, false, false, false, false, true, false, true, false, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [true, true, true, false, false, false, false, false, false] true [true, false, true, false, false, true, true, false, true, false, true] 7 h16 first_segment_17)
  have h18 : P [false, false, false, true] false [true, false, true, false, false, true, true, false, true, false, true] := by
    simpa [windowLeft, trimRight, run, step, moveL, moveR] using
      (hclosed [false, false, false, false] false [true, false, false, false, false, true, false, true, false, false, true, true, false, true, false, true] 5 h17 first_segment_18)
  simpa [windowLeft, trimRight, run, step, moveL, moveR] using
    (hclosed [false, false, false, true] false [true, false, true, false, false, true, true, false, true, false, true] 5 h18 first_segment_19)

theorem no_safe_left_four_window
    (P : List Bool → Bool → List Bool → Prop)
    (hblank : P [false,false,false,false] false [])
    (hclosed : FirstWindowClosed 4 P)
    (hsafe : ∀ ls rs, ¬ P ls false (true :: true :: rs)) : False := by
  exact hsafe [false, true, false, true] [false, true, false, true]
    (left_four_window_forces_halt_guard P hblank hclosed)

/-- Truncating the four-bit physical left window preserves every shorter
    left window; this elementary lemma transports the no-go to all k ≤ 4. -/
private theorem left_small_k (k : Nat) (hk : k ≤ 4) (ls : List Bool) :
    windowLeft k (windowLeft 4 ls) = windowLeft k ls := by
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hkcases with h | h | h | h | h <;> subst k
  all_goals
    cases ls with
    | nil => simp [windowLeft, List.replicate]
    | cons a l1 =>
      cases l1 with
      | nil => simp [windowLeft, List.replicate]
      | cons b l2 =>
        cases l2 with
        | nil => simp [windowLeft, List.replicate]
        | cons c l3 =>
          cases l3 with
          | nil => simp [windowLeft, List.replicate]
          | cons d l4 => simp [windowLeft, List.replicate]

/-- For every k ≤ 4, no universal first-return invariant based on k
    nearest-left bits, the head bit, and the full right tape can contain
    blank and rule out every A0/right11 halting projection. -/
theorem no_safe_window_le_four
    (k : Nat) (hk : k ≤ 4)
    (P : List Bool → Bool → List Bool → Prop)
    (hblank : P (windowLeft k []) false [])
    (hclosed : FirstWindowClosed k P)
    (hsafe : ∀ ls rs, ¬ P ls false (true :: true :: rs)) : False := by
  let Q : List Bool → Bool → List Bool → Prop :=
    fun ls h rs => P (windowLeft k ls) h rs
  have qblank : Q [false,false,false,false] false [] := by
    dsimp [Q]
    have h4 : windowLeft 4 ([] : List Bool) = [false,false,false,false] := by decide
    rw [← h4, left_small_k k hk]
    exact hblank
  have qclosed : FirstWindowClosed 4 Q := by
    intro ls h rs n hp hfirst
    dsimp [Q] at hp ⊢
    have hp0 : P (windowLeft k ls) h (trimRight rs) := by
      simpa [left_small_k k hk] using hp
    have hnext := hclosed ls h rs n hp0 hfirst
    simpa [left_small_k k hk] using hnext
  have qsafe : ∀ ls rs, ¬ Q ls false (true :: true :: rs) := by
    intro ls rs hp
    exact hsafe (windowLeft k ls) rs hp
  exact no_safe_left_four_window Q qblank qclosed qsafe

end BB6.Row262.Window

#print axioms BB6.Row262.Window.left_four_window_forces_halt_guard
#print axioms BB6.Row262.Window.no_safe_left_four_window
#print axioms BB6.Row262.Window.no_safe_window_le_four
