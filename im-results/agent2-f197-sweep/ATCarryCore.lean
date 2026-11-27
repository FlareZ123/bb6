import MacroExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace F197
open Q

/- Literal transducer rules for the P^n-carried complementary-AT family.
   Nearest-first A=10,T=1100,J=100,C=110,u=1111000,s=11111000,
   t=111000,d=11,e=1; B right has its two guaranteed zero bits
   before the shown shortened run stack.
   Generic right continuations require a true first bit; this is essential.
   All statements are exact source-machine primitive-run identities. -/

/-- AAT/e -> /ud in 36 live steps. -/
theorem atc_consume_e (l : Tape) (hl : l 0 = true) :
    run 36
      (other B (pre [ true, false, true, false, true, true, false, false ] l) (pre [ false, false, true ] blank)) =
    some (other B (pre [  ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, false, true, true, false, false ] l, pre [ false, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [  ] l, pre [ false, false, true, true, true, true, false, false, false, true, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 13 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 13 m 36 m' hv hc

/-- AAT/uR -> /usR in 36 live steps. -/
theorem atc_consume_u (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 36
      (other B (pre [ true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [  ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, false, true, true, false, false ] l, pre [ false, false, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [  ] l, pre [ false, false, true, true, true, true, false, false, false, true, true, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 13 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 13 m 36 m' hv hc

/-- AAA/uCR -> J/AsCR in 47 live steps. -/
theorem atc_term_A (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 47
      (other B (pre [ true, false, true, false, true, false ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false ] l, pre [ false, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (47, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 14 m 47 m' hv hc

/-- TAA/uCR -> J/ACuCR in 57 live steps. -/
theorem atc_term_T (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 57
      (other B (pre [ true, true, false, false, true, false, true, false ] l) (pre [ false, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, false, true, false ] l, pre [ false, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (57, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 57 m' hv hc

/-- J/AuuCR -> JAT/AsCR in 60 live steps. -/
theorem atc_peel_AA (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 60
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 60 m' hv hc

/-- J/AuAuCR -> JAT/ACuCR in 60 live steps. -/
theorem atc_peel_AT (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 60
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (60, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 60 m' hv hc

/-- J/ACtuCR -> JAAT/AsCR in 64 live steps. -/
theorem atc_peel_TA (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 64
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 64 m' hv hc

/-- J/ACtAuCR -> JAAT/ACuCR in 64 live steps. -/
theorem atc_peel_TT (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 64
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, false, false, false, true, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (64, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 64 m' hv hc

/-- J/AsCR -> JAAT/ACR in 32 live steps. -/
theorem atc_junction_A (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 32
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (32, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 8 m 32 m' hv hc

/-- J/ACuCR -> JAAAT/ACR in 36 live steps. -/
theorem atc_junction_T (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 36
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 9 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 9 m 36 m' hv hc

/-- J/ACuR -> JAAAT/AR in 36 live steps. -/
theorem atc_counter_u (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 36
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 9 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 9 m 36 m' hv hc

/-- J/AsR -> JAAT/AR in 32 live steps. -/
theorem atc_counter_s (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 32
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (32, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 8 m 32 m' hv hc

/-- J/Ad -> AAT/e in 27 live steps. -/
theorem atc_counter_d (l : Tape) (hl : l 0 = true) :
    run 27
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true ] blank)) =
    some (other B (pre [ true, false, true, false, true, true, false, false ] l) (pre [ false, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, true, false, true, true, false, false ] l, pre [ false, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 7 m = some (27, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 7 m 27 m' hv hc

/-- Universal 46-step TAT prefix removal with an arbitrary run-aligned right carry. -/
theorem atc_preconsume (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 46
      (other B (pre [ true, true, false, false, true, false, true, true, false, false ] l) (pre [ false, false ] r)) =
    some (other B l (pre [ false, false, true, true, true, true, false, false, false, true, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, false, true, true, false, false ] l, pre [ false, false ] r⟩
  let m' : MacroConfig := ⟨.B, l, pre [ false, false, true, true, true, true, false, false, false, true, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 16 m = some (46, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 16 m 46 m' hv hc

/-- Final C/e right carry decodes an AAAT output at exact cost 31. -/
theorem atc_counter_base (l : Tape) (hl : l 0 = true) :
    run 31
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true ] blank)) =
    some (other B (pre [ true, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true ] blank)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true ] blank⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true ] blank⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (31, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 8 m 31 m' hv hc

#print axioms atc_counter_base

/-- Generic aligned-right terminal AAA/uR, source-exact. -/
theorem atc_terminal_A_u (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 47
      (other B (pre [ true, false, true, false, true, false ] l) (pre [ false, false, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, true, false, true, false ] l, pre [ false, false, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 14 m = some (47, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 14 m 47 m' hv hc

#print axioms atc_terminal_A_u

/-- Generic aligned-right terminal TAA/uR, source-exact. -/
theorem atc_terminal_T_u (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 57
      (other B (pre [ true, true, false, false, true, false, true, false ] l) (pre [ false, false, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, true, false, false, true, false, true, false ] l, pre [ false, false, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 17 m = some (57, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 17 m 57 m' hv hc

#print axioms atc_terminal_T_u

/-- Full right-tail generic terminal decoder J/AsR. -/
theorem atc_junction_A_general (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 32
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 8 m = some (32, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 8 m 32 m' hv hc

#print axioms atc_junction_A_general

/-- Full right-tail generic terminal decoder J/ACuR. -/
theorem atc_junction_T_general (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run 36
      (other B (pre [ true, false, false ] l) (pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false ] r)) =
    some (other B (pre [ true, false, false, true, false, true, false, true, false, true, true, false, false ] l) (pre [ false, false, true, false ] r)) := by
  let m : MacroConfig := ⟨.B, pre [ true, false, false ] l, pre [ false, false, true, false, true, true, false, true, true, true, true, false, false, false ] r⟩
  let m' : MacroConfig := ⟨.B, pre [ true, false, false, true, false, true, false, true, false, true, true, false, false ] l, pre [ false, false, true, false ] r⟩
  have hv : valid m := by rfl
  have hc : macroRunExact 9 m = some (36, m') := by
    dsimp [m, m']
    rw [← decompose_bit l true hl, ← decompose_bit r true hr]
    rfl
  simpa [m, m', physical] using macroRunExact_sound 9 m 36 m' hv hc

#print axioms atc_junction_T_general

#print axioms atc_preconsume

#print axioms atc_consume_e
#print axioms atc_consume_u
#print axioms atc_term_A
#print axioms atc_term_T
#print axioms atc_peel_AA
#print axioms atc_peel_AT
#print axioms atc_peel_TA
#print axioms atc_peel_TT
#print axioms atc_junction_A
#print axioms atc_junction_T
#print axioms atc_counter_u
#print axioms atc_counter_s
#print axioms atc_counter_d

end F197
