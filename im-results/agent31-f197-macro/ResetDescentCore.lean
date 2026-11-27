import Macro

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197

/-
Run alphabet used below:
  A=(1,1), J=(1,2), T=(2,2), P=AAT,
  s=(5,3), u=(4,3), x=(1,1), d=(2,e), e=(1,e).
All Boolean prefixes are nearest-first.  The dominant reachable descent always
has suffix beginning T A; exposing those two run symbols makes the literal
primitive computation definitionally fixed.
-/

/-- n >= 4 middle core: after consuming P^n, the remaining right word starts
    u s s s ... .  This consumes exactly the first u s s and preserves the
    next s and all later suffix. -/
theorem reset_descent_middle_s_321 (l r : Tape) :
    run 321
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false, true, true, false, false, true, false] l)
        (pre [false, false, true, true, true, true, false, false, false, true,
              true, true, true, true, false, false, false, true, true,
              true, true, true, false, false, false, true, true, true,
              true, true, false, false, false] r)) =
    some
      (other B
        (pre [true, false, false, true, false, false, true, true, false,
              false, true, false, true, false, true, true, false, false,
              true, false, true, false, true, false, true, true, false,
              false, true, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, true, false,
              false, true, false] l)
        (pre [false, false, true, false, true, true, true, true, true, false,
              false, false] r)) := by
  simp [run, step, moveR, moveL, other, tail, cons, pre]

/-- n = 3 middle core, where the preserved right suffix is the terminal d. -/
theorem reset_descent_middle_d_321 (l : Tape) :
    run 321
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false, true, true, false, false, true, false] l)
        (pre [false, false, true, true, true, true, false, false, false, true,
              true, true, true, true, false, false, false, true, true,
              true, true, true, false, false, false, true, true] blank)) =
    some
      (other B
        (pre [true, false, false, true, false, false, true, true, false,
              false, true, false, true, false, true, true, false, false,
              true, false, true, false, true, false, true, true, false,
              false, true, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, true, false,
              false, true, false] l)
        (pre [false, false, true, false, true, true] blank)) := by
  simp [run, step, moveR, moveL, other, tail, cons, pre]

/-- n = 2 endpoint after the P-consumer: u s d is exhausted and the machine
    returns directly to right e, appending K=TATP on the left. -/
theorem reset_descent_n2_middle_316 (l : Tape) :
    run 316
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false, true, true, false, false, true, false] l)
        (pre [false, false, true, true, true, true, false, false, false, true,
              true, true, true, true, false, false, false, true, true] blank)) =
    some
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false, true, true, false, false, true, false,
              true, true, false, false, true, false, true, false, true,
              true, false, false, true, true, false, false, true, false] l)
        (pre [false, false, true] blank)) := by
  simp [run, step, moveR, moveL, other, tail, cons, pre]

#print axioms reset_descent_middle_s_321
#print axioms reset_descent_middle_d_321
#print axioms reset_descent_n2_middle_316

end F197
