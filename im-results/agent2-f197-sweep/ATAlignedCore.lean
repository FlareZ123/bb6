import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/- Source-verified scanner/decoder transducer rules.  Both unconsumed
   left and right tails are run-aligned (their first bits are true).
   This explicit domain is needed to avoid arbitrary-tape sorryAx.
   e=1, A=10, T=1100, J=100, C=110, u=1111000, t=111000. -/

/-- AT /  ->  / t, 8 live steps. -/
theorem scan_AT_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 8
      (other B (pre [ true, false, true, true, false, false ] l) (pre [ false, false ] r)) =
    some (other B (pre [  ] l) (pre [ false, false, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, true, false, false ] l, pre [ false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [  ] l, pre [ false, false, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 5 m = some (8, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 5 m 8 m' hv hc

/-- TT /  ->  / tA, 18 live steps. -/
theorem scan_TT_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 18
      (other B (pre [ true, true, false, false, true, true, false, false ] l) (pre [ false, false ] r)) =
    some (other B (pre [  ] l) (pre [ false, false, true, true, true, false, false, false, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, true, false, false ] l, pre [ false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [  ] l, pre [ false, false, true, true, true, false, false, false, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (18, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 8 m 18 m' hv hc

/-- AAA / t -> J / Au, 47 live steps. -/
theorem term_A_t_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 47
      (other B (pre [ true, false, true, false, true, false ] l) (pre [ false, false, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false ] l, pre [ false, false, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (47, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 14 m 47 m' hv hc

/-- TAA / t -> J / ACt, 57 live steps. -/
theorem term_T_t_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 57
      (other B (pre [ true, true, false, false, true, false, true, false ] l) (pre [ false, false, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, false, true, false ] l, pre [ false, false, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (57, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 57 m' hv hc

/-- J / Aut -> JAT / Au, 60 live steps. -/
theorem peel_A_t_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 60
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 60 m' hv hc

/-- J / AuAt -> JAT / ACt, 60 live steps. -/
theorem peel_A_At_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 60
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 60 m' hv hc

/-- J / ACtt -> JAAT / Au, 64 live steps. -/
theorem peel_T_t_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 64
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 64 m' hv hc

/-- J / ACtAt -> JAAT / ACt, 64 live steps. -/
theorem peel_T_At_aligned (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 64
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 64 m' hv hc

#print axioms scan_AT_aligned
#print axioms scan_TT_aligned
#print axioms term_A_t_aligned
#print axioms term_T_t_aligned
#print axioms peel_A_t_aligned
#print axioms peel_A_At_aligned
#print axioms peel_T_t_aligned
#print axioms peel_T_At_aligned

end F197
