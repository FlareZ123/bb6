import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197

/-
Terminal scanner cores for the paired-prefix family.
A=(1,1), T=(2,2), J=(1,2), t=(3,3), x=(1,1),
u=(4,3), C=(2,1), d=(2,e), e=(1,e).
-/

theorem terminal_A_e (l : Tape) :
    run 47
      (other B
        (pre [true,false,true,false,true,false] l)
        (pre [false,false,true] blank)) =
    some
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,true,false,true,false] l,
    pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (47,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 14 m 47 m' hv hc

theorem terminal_A_t (l r : Tape) :
    run 47
      (other B
        (pre [true,false,true,false,true,false] l)
        (pre [false,false,true,true,true,false,false,false] r)) =
    some
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,true,false,true,false] l,
    pre [false,false,true,true,true,false,false,false] r⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (47,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 14 m 47 m' hv hc

theorem terminal_T_e (l : Tape) :
    run 57
      (other B
        (pre [true,true,false,false,true,false,true,false] l)
        (pre [false,false,true] blank)) =
    some
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,true,false,false,true,false,true,false] l,
    pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (57,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 17 m 57 m' hv hc

theorem terminal_T_t (l r : Tape) :
    run 57
      (other B
        (pre [true,true,false,false,true,false,true,false] l)
        (pre [false,false,true,true,true,false,false,false] r)) =
    some
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,true,false,false,true,false,true,false] l,
    pre [false,false,true,true,true,false,false,false] r⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (57,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 17 m 57 m' hv hc

#print axioms terminal_A_e
#print axioms terminal_A_t
#print axioms terminal_T_e
#print axioms terminal_T_t

end F197
