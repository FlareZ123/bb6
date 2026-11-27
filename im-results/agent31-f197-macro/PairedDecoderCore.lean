import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197

/-
Exact local decoder-peel rules for the paired-prefix reset family.

Run notation (nearest first):
  A=(1,1), J=(1,2), T=(2,2), C=(2,1),
  u=(4,3), t=(3,3), x=(1,1), e=(1,e), d=(2,e).

At a B boundary the literal Macro.lean right stack is
0 :: (shortened right), hence the two leading false bits before x below.
-/

theorem peelA_u_t (l r : Tape) :
    run 60
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,true,true,false,false,false,
              true,true,true,false,false,false] r)) =
    some (other B
      (pre [true,false,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false,
         true,true,true,false,false,false] r⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 16 m 60 m' hv hc

theorem peelA_u_At (l r : Tape) :
    run 60
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,true,true,false,false,false,
              true,false,true,true,true,false,false,false] r)) =
    some (other B
      (pre [true,false,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true,false,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false,
         true,false,true,true,true,false,false,false] r⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 16 m 60 m' hv hc

theorem peelT_Ct_t (l r : Tape) :
    run 64
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true,true,true,false,false,false,
              true,true,true,false,false,false] r)) =
    some (other B
      (pre [true,false,false,true,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false,
         true,true,true,false,false,false] r⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 17 m 64 m' hv hc

theorem peelT_Ct_At (l r : Tape) :
    run 64
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true,true,true,false,false,false,
              true,false,true,true,true,false,false,false] r)) =
    some (other B
      (pre [true,false,false,true,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true,false,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false,
         true,false,true,true,true,false,false,false] r⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 17 m 64 m' hv hc

theorem peelA_u_e (l : Tape) :
    run 60
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,true,true,false,false,false,true] blank)) =
    some (other B
      (pre [true,false,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 16 m 60 m' hv hc

theorem peelA_u_Ae (l : Tape) :
    run 60
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,true,true,false,false,false,
              true,false,true] blank)) =
    some (other B
      (pre [true,false,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true,false,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,true,true,false,false,false,
         true,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 16 m 60 m' hv hc

theorem peelT_Ct_e (l : Tape) :
    run 64
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true,true,true,false,false,false,true] blank)) =
    some (other B
      (pre [true,false,false,true,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 17 m 64 m' hv hc

theorem peelT_Ct_Ae (l : Tape) :
    run 64
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true,true,true,false,false,false,
              true,false,true] blank)) =
    some (other B
      (pre [true,false,false,true,false,true,false,true,true,false,false] l)
      (pre [false,false,true,false,true,true,false,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true,true,true,false,false,false,
         true,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,false,true,false,true,false,true,true,false,false] l,
    pre [false,false,true,false,true,true,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 17 m 64 m' hv hc

/-- Decoder base for leading data bit T: x·C·e becomes A A A T. -/
theorem decoder_base_T (l : Tape) :
    run 31
      (other B
        (pre [true,false,false] l)
        (pre [false,false,true,false,true,true,false,true] blank)) =
    some
      (other B
        (pre [true,false,true,false,true,false,true,true,false,false] l)
        (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,false] l,
    pre [false,false,true,false,true,true,false,true] blank⟩
  let m' : MacroConfig := ⟨.B,
    pre [true,false,true,false,true,false,true,true,false,false] l,
    pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (31,m') := by
    dsimp [m,m']; rw [← decompose l]; rfl
  simpa [m,m',physical] using macroRunExact_sound 8 m 31 m' hv hc

#print axioms decoder_base_T
#print axioms peelA_u_t
#print axioms peelA_u_At
#print axioms peelT_Ct_t
#print axioms peelT_Ct_At
#print axioms peelA_u_e
#print axioms peelA_u_Ae
#print axioms peelT_Ct_e
#print axioms peelT_Ct_Ae

end F197
