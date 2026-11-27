import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-- Boundary of an even P-descent: J becomes TT at reset right e. -/
theorem reset_J_to_TT (l : Tape) (hl : l 0 = true) :
    run 21
      (other B (pre [true, false, false] l)
        (pre [false, false, true] blank)) =
    some
      (other B
        (pre [true, true, false, false, true, true, false, false] l)
        (pre [false, false, true] blank)) := by
  let m : MacroConfig :=
    ⟨.B, pre [true, false, false] l, pre [false, false, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B, pre [true, true, false, false, true, true, false, false] l,
      pre [false, false, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 6 m = some (21, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 6 m 21 m' hv hc

/-- Boundary of an odd P-descent: PJ becomes AUJT. -/
theorem reset_PJ_to_AUJT (l : Tape) (hl : l 0 = true) :
    run 75
      (other B
        (pre [true, false, true, false, true, true, false, false,
              true, false, false] l)
        (pre [false, false, true] blank)) =
    some
      (other B
        (pre [true, false, true, true, true, false, false, true, false,
              false, true, true, false, false] l)
        (pre [false, false, true] blank)) := by
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, true, false, true, true, false, false,
           true, false, false] l,
      pre [false, false, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, false, true, true, true, false, false, true, false,
           false, true, true, false, false] l,
      pre [false, false, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 22 m = some (75, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 22 m 75 m' hv hc

/-- The AUJ boundary then becomes TTJT. -/
theorem reset_AUJ_to_TTJT (l : Tape) (hl : l 0 = true) :
    run 39
      (other B
        (pre [true, false, true, true, true, false, false, true, false,
              false] l)
        (pre [false, false, true] blank)) =
    some
      (other B
        (pre [true, true, false, false, true, true, false, false, true,
              false, false, true, true, false, false] l)
        (pre [false, false, true] blank)) := by
  let m : MacroConfig :=
    ⟨.B,
      pre [true, false, true, true, true, false, false, true, false,
           false] l,
      pre [false, false, true] blank⟩
  let m' : MacroConfig :=
    ⟨.B,
      pre [true, true, false, false, true, true, false, false, true,
           false, false, true, true, false, false] l,
      pre [false, false, true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (39, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 14 m 39 m' hv hc

#print axioms reset_J_to_TT
#print axioms reset_PJ_to_AUJT
#print axioms reset_AUJ_to_TTJT

end F197
