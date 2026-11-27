import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/-
Exact scanner cores for the paired-prefix reset parser.
At B boundaries used here the literal macro right stack begins with two zeros.
A=(1,1), T=(2,2), t=(3,3), x=(1,1).
-/

/-- Scanning packet A T deposits one t=(3,3) token on the right. -/
theorem scan_AT (l r : Tape) :
    run 8
      (other B
        (pre [true,false,true,true,false,false] l)
        (pre [false,false] r)) =
    some
      (other B l
        (pre [false,false,true,true,true,false,false,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,false,true,true,false,false] l,
    pre [false,false] r⟩
  let m' : MacroConfig := ⟨.B, l,
    pre [false,false,true,true,true,false,false,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 5 m = some (8,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 5 m 8 m' hv hc

/-- Scanning packet T T deposits t x on the right. -/
theorem scan_TT (l r : Tape) :
    run 18
      (other B
        (pre [true,true,false,false,true,true,false,false] l)
        (pre [false,false] r)) =
    some
      (other B l
        (pre [false,false,true,true,true,false,false,false,true,false] r)) := by
  let m : MacroConfig := ⟨.B,
    pre [true,true,false,false,true,true,false,false] l,
    pre [false,false] r⟩
  let m' : MacroConfig := ⟨.B, l,
    pre [false,false,true,true,true,false,false,false,true,false] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (18,m') := by
    dsimp [m,m']; rw [← decompose l, ← decompose r]; rfl
  simpa [m,m',physical] using macroRunExact_sound 8 m 18 m' hv hc

#print axioms scan_AT
#print axioms scan_TT

end F197
