import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
Two independent original-machine exact reset identities for the complementary
TAT branch.  A=10, T=1100 in nearest-first bits, reset e=1.

TAT A A A X -> A A A T A A T X, 156 primitive live steps
TAT T A A X -> A A A T A A A T X, 170 primitive live steps

X is arbitrary except that its first bit is 1 (a well-formed run word).
This hypothesis is essential for the no-sorryAx evaluation domain.
-/

theorem reset_TATAAA (l : Tape) (hl : l 0 = true) :
    run 156
      (other B
        (pre [true,true,false,false,true,false,true,true,false,false,
              true,false,true,false,true,false] l)
        (pre [false,false,true] blank)) =
    some
      (other B
        (pre [true,false,true,false,true,false,true,true,false,false,
              true,false,true,false,true,true,false,false] l)
        (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,true,false,false,true,false,true,true,false,false,
         true,false,true,false,true,false] l,
    pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,true,false,true,false,true,true,false,false,
         true,false,true,false,true,true,false,false] l,
    pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 46 m = some (156, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 46 m 156 m' hv hc

theorem reset_TATTAA (l : Tape) (hl : l 0 = true) :
    run 170
      (other B
        (pre [true,true,false,false,true,false,true,true,false,false,
              true,true,false,false,true,false,true,false] l)
        (pre [false,false,true] blank)) =
    some
      (other B
        (pre [true,false,true,false,true,false,true,true,false,false,
              true,false,true,false,true,false,true,true,false,false] l)
        (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,true,false,false,true,false,true,true,false,false,
         true,true,false,false,true,false,true,false] l,
    pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,true,false,true,false,true,true,false,false,
         true,false,true,false,true,false,true,true,false,false] l,
    pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 50 m = some (170, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 50 m 170 m' hv hc

#print axioms reset_TATAAA
#print axioms reset_TATTAA

end F197
