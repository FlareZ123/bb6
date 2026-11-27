import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197

/-
Run alphabet:
  A=(1,1), J=(1,2), T=(2,2), P=AAT,
  s=(5,3), u=(4,3), x=(1,1), d=(2,e), e=(1,e).
Boolean prefixes are nearest-first.  The reachable descent suffix begins T A.
The proofs execute 95 (or 94) exact four-phase macro steps and lift them back
to the literal machine with macroRunExact_sound.
-/

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
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, true, false, false, true, false,
           true, false, true, true, false, false, true, false, true,
           false, true, false, true, true, false, false, true, false] l,
      pre [false, false, true, true, true, true, false, false, false, true,
           true, true, true, true, false, false, false, true, true,
           true, true, true, false, false, false, true, true, true,
           true, true, false, false, false] r⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, false, false, true, true, false,
           false, true, false, true, false, true, true, false, false,
           true, false, true, false, true, false, true, true, false,
           false, true, false, true, true, false, false, true, false,
           true, false, true, true, false, false, true, true, false,
           false, true, false] l,
      pre [false, false, true, false, true, true, true, true, true, false,
           false, false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 95 m = some (321, m') := by
    dsimp [m, m']
    rw [← decompose l, ← decompose r]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 95 m 321 m' hv hc

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
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, true, false, false, true, false,
           true, false, true, true, false, false, true, false, true,
           false, true, false, true, true, false, false, true, false] l,
      pre [false, false, true, true, true, true, false, false, false, true,
           true, true, true, true, false, false, false, true, true,
           true, true, true, false, false, false, true, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, false, false, true, true, false,
           false, true, false, true, false, true, true, false, false,
           true, false, true, false, true, false, true, true, false,
           false, true, false, true, true, false, false, true, false,
           true, false, true, true, false, false, true, true, false,
           false, true, false] l,
      pre [false, false, true, false, true, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 95 m = some (321, m') := by
    dsimp [m, m']
    rw [← decompose l]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 95 m 321 m' hv hc

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
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, true, false, false, true, false,
           true, false, true, true, false, false, true, false, true,
           false, true, false, true, true, false, false, true, false] l,
      pre [false, false, true, true, true, true, false, false, false, true,
           true, true, true, true, false, false, false, true, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, false, false, true, true, false, false, true, false,
           true, false, true, true, false, false, true, false, true,
           false, true, false, true, true, false, false, true, false,
           true, true, false, false, true, false, true, false, true,
           true, false, false, true, true, false, false, true, false] l,
      pre [false, false, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 94 m = some (316, m') := by
    dsimp [m, m']
    rw [← decompose l]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 94 m 316 m' hv hc

#print axioms reset_descent_middle_s_321
#print axioms reset_descent_middle_d_321
#print axioms reset_descent_n2_middle_316

end F197
