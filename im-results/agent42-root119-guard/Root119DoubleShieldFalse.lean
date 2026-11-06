import Root119BShift
namespace BB6Root119

/-- The deliberately synthetic B/0 tape has marks at -6, -3 and -1. -/
def doubleTape (x : Int) : Bool := decide (x = -6 ∨ x = -3 ∨ x = -1)
def doubleStart : Conf := ⟨.B, 0, doubleTape⟩

/-- A forbidden 1000 or 1100 word ending at or before the B-head. -/
def DoubleForbidden (c : Conf) (p : Bool) : Prop :=
  ∃ x : Int, x+3 ≤ c.h ∧ c.tape x = true ∧
    c.tape (x+1) = p ∧ c.tape (x+2) = false ∧ c.tape (x+3) = false

theorem double_no_1000 : ¬ DoubleForbidden doubleStart false := by
  rintro ⟨x, hx, h0, h1, h2, h3⟩
  have heq : x = -6 ∨ x = -3 ∨ x = -1 := by
    simpa [doubleStart, doubleTape] using h0
  rcases heq with h | h | h
  · subst x
    simp [doubleStart, doubleTape] at h3
  · subst x
    simp [doubleStart, doubleTape] at h2
  · change x+3 ≤ 0 at hx
    omega

theorem double_no_1100 : ¬ DoubleForbidden doubleStart true := by
  rintro ⟨x, hx, h0, h1, h2, h3⟩
  have heq : x = -6 ∨ x = -3 ∨ x = -1 := by
    simpa [doubleStart, doubleTape] using h0
  rcases heq with h | h | h
  · subst x
    simp [doubleStart, doubleTape] at h1
  · subst x
    simp [doubleStart, doubleTape] at h1
  · change x+3 ≤ 0 at hx
    omega

def doubleAfter : Conf := (run 23 doubleStart).getD doubleStart

theorem double_23 : run 23 doubleStart = some doubleAfter := by
  rfl

theorem doubleAfter_is_B_zero :
    doubleAfter.q = .B ∧ doubleAfter.h = 3 ∧
    doubleAfter.tape doubleAfter.h = false := by
  decide

theorem doubleAfter_has_1000 : DoubleForbidden doubleAfter false := by
  refine ⟨-6, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Both local forbidden-word shields can fail jointly after a genuine 23-step
    source-table B/0 first return on a synthetic tape. No blank reachability
    is asserted; the true blank orbit requires more history in its invariant. -/
theorem double_shield_not_closed :
  doubleStart.q = .B ∧ doubleStart.tape doubleStart.h = false ∧
  ¬DoubleForbidden doubleStart false ∧ ¬DoubleForbidden doubleStart true ∧
  run 23 doubleStart = some doubleAfter ∧ doubleAfter.q = .B ∧
  doubleAfter.tape doubleAfter.h = false ∧
  DoubleForbidden doubleAfter false := by
  exact ⟨rfl, by decide, double_no_1000, double_no_1100,
    double_23, doubleAfter_is_B_zero.1, doubleAfter_is_B_zero.2.2,
    doubleAfter_has_1000⟩

#print axioms BB6Root119.double_shield_not_closed
end BB6Root119
