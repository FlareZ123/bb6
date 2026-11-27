import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
At a B boundary the accelerated sweep coordinate omits one guaranteed zero
between the current cell and its shortened right word.  Thus the Macro.lean
right stack is 0 :: (shortened sweep right).  These proofs execute the exact
verified macro semantics and then appeal to macroRunExact_sound.
-/

theorem reset_P_consume_us (l r : Tape) :
    run 36
      (other B
        (pre [true, false, true, false, true, true, false, false] l)
        (pre [false, false, true, true, true, true, false, false, false] r)) =
    some
      (other B l
        (pre [false, false, true, true, true, true, false, false, false,
              true, true, true, true, true, false, false, false] r)) := by
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, true, false, true, true, false, false] l,
      pre [false, false, true, true, true, true, false, false, false] r⟩
  let m' : MacroConfig :=
    ⟨.B, l,
      pre [false, false, true, true, true, true, false, false, false,
           true, true, true, true, true, false, false, false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 13 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose l, ← decompose r]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 13 m 36 m' hv hc

theorem reset_P_consume_e (l : Tape) :
    run 36
      (other B
        (pre [true, false, true, false, true, true, false, false] l)
        (pre [false, false, true] blank)) =
    some
      (other B l
        (pre [false, false, true, true, true, true, false, false, false,
              true, true] blank)) := by
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, true, false, true, true, false, false] l,
      pre [false, false, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B, l,
      pre [false, false, true, true, true, true, false, false, false,
           true, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 13 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose l]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 13 m 36 m' hv hc

theorem reset_decoder_s (l r : Tape) :
    run 32
      (other B
        (pre [true, false, false] l)
        (pre [false, false, true, false, true, true, true, true, true,
              false, false, false] r)) =
    some
      (other B
        (pre [true, false, false, true, false, true, false, true, true,
              false, false] l)
        (pre [false, false, true, false] r)) := by
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, false] l,
      pre [false, false, true, false, true, true, true, true, true,
           false, false, false] r⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, false, true, false, true, true,
           false, false] l,
      pre [false, false, true, false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (32, m') := by
    dsimp [m, m']
    rw [← decompose l, ← decompose r]
    simp [macroRunExact, macroStep, pre, tail, cons]
  simpa [m, m', physical] using macroRunExact_sound 8 m 32 m' hv hc

theorem reset_decoder_d (l : Tape) :
    run 27
      (other B
        (pre [true, false, false] l)
        (pre [false, false, true, false, true, true] blank)) =
    some
      (other B
        (pre [true, false, true, false, true, true, false, false] l)
        (pre [false, false, true] blank)) := by
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, false] l,
      pre [false, false, true, false, true, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, false, true, false, true, true, false, false] l,
      pre [false, false, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 7 m = some (27, m') := by
    dsimp [m, m']
    rw [← decompose l]
    simp [macroRunExact, macroStep, pre, tail, cons]
  simpa [m, m', physical] using macroRunExact_sound 7 m 27 m' hv hc

#print axioms reset_P_consume_us
#print axioms reset_P_consume_e
#print axioms reset_decoder_s
#print axioms reset_decoder_d

end F197
