import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/- Complementary-AT reset transducer literal-source components.
   At B the right macro stack is two zeros followed by the encoded run word.
   A=10, T=1100, J=100, C=110, u=1111000, s=11111000,
   t=111000, e=1 (all written nearest first).
   Each lemma is independent of the run-aligned suffix beyond its first bit.
   No finite scan or assumed no-halt property enters the proof. -/

/-- TAT · X, e ->  · X, uCe: 46 literal live steps. -/
theorem at_preconsume (l : Tape) (hl : l 0 = true) :
    run 46
      (other B (pre [ true, true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true ] blank)) =
    some (other B (pre [  ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [  ] l, pre [ false, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (46, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 46 m' hv hc

/-- AAA · X, uCe -> J · X, AsCe: 47 literal live steps. -/
theorem at_term_A (l : Tape) (hl : l 0 = true) :
    run 47
      (other B (pre [ true, false, true, false, true, false ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false ] l, pre [ false, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (47, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 14 m 47 m' hv hc

/-- TAA · X, uCe -> J · X, ACuCe: 57 literal live steps. -/
theorem at_term_T (l : Tape) (hl : l 0 = true) :
    run 57
      (other B (pre [ true, true, false, false, true, false, true, false ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, false, true, false ] l, pre [ false, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (57, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 57 m' hv hc

/-- J · X, AuuCe -> JAT · X, AsCe: 60 literal live steps. -/
theorem at_peel_AA (l : Tape) (hl : l 0 = true) :
    run 60
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 60 m' hv hc

/-- J · X, AuAuCe -> JAT · X, ACuCe: 60 literal live steps. -/
theorem at_peel_AT (l : Tape) (hl : l 0 = true) :
    run 60
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 60 m' hv hc

/-- J · X, ACtuCe -> JAAT · X, AsCe: 64 literal live steps. -/
theorem at_peel_TA (l : Tape) (hl : l 0 = true) :
    run 64
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 64 m' hv hc

/-- J · X, ACtAuCe -> JAAT · X, ACuCe: 64 literal live steps. -/
theorem at_peel_TT (l : Tape) (hl : l 0 = true) :
    run 64
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 64 m' hv hc

/-- J · X, AsCe -> AAATAAT · X, e: 63 literal live steps. -/
theorem at_base_A (l : Tape) (hl : l 0 = true) :
    run 63
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (63, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 63 m' hv hc

/-- J · X, ACuCe -> AAATAAAT · X, e: 67 literal live steps. -/
theorem at_base_T (l : Tape) (hl : l 0 = true) :
    run 67
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (67, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 67 m' hv hc

#print axioms at_preconsume
#print axioms at_term_A
#print axioms at_term_T
#print axioms at_peel_AA
#print axioms at_peel_AT
#print axioms at_peel_TA
#print axioms at_peel_TT
#print axioms at_base_A
#print axioms at_base_T

end F197
