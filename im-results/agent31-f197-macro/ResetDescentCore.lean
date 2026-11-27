import Macro

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197

/-
Fixed core used by the reset descent.  The hypotheses expose only the first
bit of the two untouched suffixes; the 321-step computation never needs more.
The Boolean lists are nearest-first, in the same convention as Macro.lean.
-/
theorem reset_descent_middle_321 (l r : Tape)
    (hl : l 0 = true) (hr : r 0 = true) :
    run 321
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false] l)
        (pre [false, true, true, true, true, false, false, false, true,
              true, true, true, true, false, false, false, true, true,
              true, true, true, false, false, false] r)) =
    some
      (other B
        (pre [true, false, false, true, false, false, true, true, false,
              false, true, false, true, false, true, true, false, false,
              true, false, true, false, true, false, true, true, false,
              false, true, false, true, true, false, false, true, false,
              true, false, true, true, false, false] l)
        (pre [false, true, false] r)) := by
  rw [← decompose_bit l true hl, ← decompose_bit r true hr]
  simp [run, step, moveR, moveL, other, d, pre, tail, cons]

/-
The n=2 endpoint after the repeated-P consumer.  The right word here is
0 · u · s · d with the terminal d followed by blank; the result is the
next reset with right 0 · e.
-/
theorem reset_descent_n2_middle_316 (l : Tape) (hl : l 0 = true) :
    run 316
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false] l)
        (pre [false, true, true, true, true, false, false, false, true,
              true, true, true, true, false, false, false, true, true] blank)) =
    some
      (other B
        (pre [true, false, false, true, true, false, false, true, false,
              true, false, true, true, false, false, true, false, true,
              false, true, false, true, true, false, false, true, false,
              true, true, false, false, true, false, true, false, true,
              true, false, false] l)
        (pre [false, true] blank)) := by
  rw [← decompose_bit l true hl]
  simp [run, step, moveR, moveL, other, d, pre, tail, cons]

#print axioms reset_descent_middle_321
#print axioms reset_descent_n2_middle_316

end F197
