import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/- Machine-found candidate resets on marker-bearing prefixes. Every rule
  below is independently required to typecheck against the literal
  MacroExact source bridge, not trusted to simulation alone. -/

/-- JTA X -> TTTA X in 21 live steps; observed 5 orbit prefixes. -/
theorem marker_0 (l : Tape) (hl : l 0 = true) :
  run 21 (other B (pre [ true, false, false, true, true, false, false, true, false ] l) (pre [false,false,true] blank)) =
    some (other B (pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false ] l) (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false, true, true, false, false, true, false ] l, pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false ] l, pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 6 m = some (21, m') := by
    dsimp [m,m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m,m',physical] using macroRunExact_sound 6 m 21 m' hv hc

#print axioms marker_0

/-- JTAA X -> TTTAA X in 21 live steps; observed 5 orbit prefixes. -/
theorem marker_1 (l : Tape) (hl : l 0 = true) :
  run 21 (other B (pre [ true, false, false, true, true, false, false, true, false, true, false ] l) (pre [false,false,true] blank)) =
    some (other B (pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false ] l) (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false, true, true, false, false, true, false, true, false ] l, pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false ] l, pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 6 m = some (21, m') := by
    dsimp [m,m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m,m',physical] using macroRunExact_sound 6 m 21 m' hv hc

#print axioms marker_1

/-- JTAAT X -> TTTAAT X in 21 live steps; observed 5 orbit prefixes. -/
theorem marker_2 (l : Tape) (hl : l 0 = true) :
  run 21 (other B (pre [ true, false, false, true, true, false, false, true, false, true, false, true, true, false, false ] l) (pre [false,false,true] blank)) =
    some (other B (pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false, true, true, false, false ] l) (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false, true, true, false, false, true, false, true, false, true, true, false, false ] l, pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false, true, true, false, false ] l, pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 6 m = some (21, m') := by
    dsimp [m,m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m,m',physical] using macroRunExact_sound 6 m 21 m' hv hc

#print axioms marker_2

/-- JTAATA X -> TTTAATA X in 21 live steps; observed 5 orbit prefixes. -/
theorem marker_3 (l : Tape) (hl : l 0 = true) :
  run 21 (other B (pre [ true, false, false, true, true, false, false, true, false, true, false, true, true, false, false, true, false ] l) (pre [false,false,true] blank)) =
    some (other B (pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false, true, true, false, false, true, false ] l) (pre [false,false,true] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false, true, true, false, false, true, false, true, false, true, true, false, false, true, false ] l, pre [false,false,true] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false, true, true, false, false, true, false ] l, pre [false,false,true] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 6 m = some (21, m') := by
    dsimp [m,m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m,m',physical] using macroRunExact_sound 6 m 21 m' hv hc

#print axioms marker_3

end F197
