import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_02
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 200, 1RB1RC_1RC1LA_0RD1LC_1LD1RB_------_------; entry 9, period 6. -/
def p200 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert200 : zipCycle p200 9 6 true (-1) = true := by decide +kernel
theorem never200 (m : Machine) (hm : compatible p200 m) : NeverHalts m :=
  zipCycle_sound p200 9 6 true (-1) (by decide) cert200 m hm
#print axioms never200


/-- Third-level first-hole refinement 201, 1RB1RC_1RC1LA_0RD1RC_1LD1RB_------_------; entry 2, period 8. -/
def p201 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert201 : zipCycle p201 2 8 true (1) = true := by decide +kernel
theorem never201 (m : Machine) (hm : compatible p201 m) : NeverHalts m :=
  zipCycle_sound p201 2 8 true (1) (by decide) cert201 m hm
#print axioms never201


/-- Third-level first-hole refinement 202, 1RB1RC_1RC1LA_0RD0LD_1LD1RB_------_------; entry 1, period 12. -/
def p202 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert202 : zipCycle p202 1 12 true (1) = true := by decide +kernel
theorem never202 (m : Machine) (hm : compatible p202 m) : NeverHalts m :=
  zipCycle_sound p202 1 12 true (1) (by decide) cert202 m hm
#print axioms never202


/-- Third-level first-hole refinement 203, 1RB1RC_1RC1LA_0RD1LD_1LD1RB_------_------; entry 5, period 4. -/
def p203 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert203 : zipCycle p203 5 4 true (1) = true := by decide +kernel
theorem never203 (m : Machine) (hm : compatible p203 m) : NeverHalts m :=
  zipCycle_sound p203 5 4 true (1) (by decide) cert203 m hm
#print axioms never203


/-- Third-level first-hole refinement 204, 1RB1RC_1RC1LA_0RD0RD_1LD1RB_------_------; entry 1, period 9. -/
def p204 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert204 : zipCycle p204 1 9 true (1) = true := by decide +kernel
theorem never204 (m : Machine) (hm : compatible p204 m) : NeverHalts m :=
  zipCycle_sound p204 1 9 true (1) (by decide) cert204 m hm
#print axioms never204


/-- Third-level first-hole refinement 205, 1RB1RC_1RC1LA_0RD1RD_1LD1RB_------_------; entry 1, period 9. -/
def p205 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert205 : zipCycle p205 1 9 true (1) = true := by decide +kernel
theorem never205 (m : Machine) (hm : compatible p205 m) : NeverHalts m :=
  zipCycle_sound p205 1 9 true (1) (by decide) cert205 m hm
#print axioms never205


/-- Third-level first-hole refinement 206, 1RB0LD_1RC1LA_0RD0LA_1LD1RB_------_------; entry 1, period 15. -/
def p206 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert206 : zipCycle p206 1 15 true (0) = true := by decide +kernel
theorem never206 (m : Machine) (hm : compatible p206 m) : NeverHalts m :=
  zipCycle_sound p206 1 15 true (0) (by decide) cert206 m hm
#print axioms never206


/-- Third-level first-hole refinement 207, 1RB0LD_1RC1LA_0RD1LA_1LD1RB_------_------; entry 7, period 4. -/
def p207 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert207 : zipCycle p207 7 4 true (0) = true := by decide +kernel
theorem never207 (m : Machine) (hm : compatible p207 m) : NeverHalts m :=
  zipCycle_sound p207 7 4 true (0) (by decide) cert207 m hm
#print axioms never207


/-- Third-level first-hole refinement 208, 1RB0LD_1RC1LA_0RD0RA_1LD1RB_------_------; entry 0, period 19. -/
def p208 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert208 : zipCycle p208 0 19 true (0) = true := by decide +kernel
theorem never208 (m : Machine) (hm : compatible p208 m) : NeverHalts m :=
  zipCycle_sound p208 0 19 true (0) (by decide) cert208 m hm
#print axioms never208


/-- Third-level first-hole refinement 209, 1RB0LD_1RC1LA_0RD1RA_1LD1RB_------_------; entry 1, period 12. -/
def p209 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert209 : zipCycle p209 1 12 true (0) = true := by decide +kernel
theorem never209 (m : Machine) (hm : compatible p209 m) : NeverHalts m :=
  zipCycle_sound p209 1 12 true (0) (by decide) cert209 m hm
#print axioms never209


/-- Third-level first-hole refinement 210, 1RB0LD_1RC1LA_0RD0LB_1LD1RB_------_------; entry 13, period 1. -/
def p210 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert210 : zipCycle p210 13 1 false (-1) = true := by decide +kernel
theorem never210 (m : Machine) (hm : compatible p210 m) : NeverHalts m :=
  zipCycle_sound p210 13 1 false (-1) (by decide) cert210 m hm
#print axioms never210


/-- Third-level first-hole refinement 211, 1RB0LD_1RC1LA_0RD1LB_1LD1RB_------_------; entry 13, period 1. -/
def p211 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert211 : zipCycle p211 13 1 false (-1) = true := by decide +kernel
theorem never211 (m : Machine) (hm : compatible p211 m) : NeverHalts m :=
  zipCycle_sound p211 13 1 false (-1) (by decide) cert211 m hm
#print axioms never211


/-- Third-level first-hole refinement 212, 1RB0LD_1RC1LA_0RD0RB_1LD1RB_------_------; entry 9, period 23. -/
def p212 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert212 : zipCycle p212 9 23 true (1) = true := by decide +kernel
theorem never212 (m : Machine) (hm : compatible p212 m) : NeverHalts m :=
  zipCycle_sound p212 9 23 true (1) (by decide) cert212 m hm
#print axioms never212


/-- Third-level first-hole refinement 213, 1RB0LD_1RC1LA_0RD1RB_1LD1RB_------_------; entry 1, period 15. -/
def p213 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert213 : zipCycle p213 1 15 true (0) = true := by decide +kernel
theorem never213 (m : Machine) (hm : compatible p213 m) : NeverHalts m :=
  zipCycle_sound p213 1 15 true (0) (by decide) cert213 m hm
#print axioms never213


/-- Third-level first-hole refinement 214, 1RB0LD_1RC1LA_0RD0LC_1LD1RB_------_------; entry 14, period 1. -/
def p214 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert214 : zipCycle p214 14 1 false (0) = true := by decide +kernel
theorem never214 (m : Machine) (hm : compatible p214 m) : NeverHalts m :=
  zipCycle_sound p214 14 1 false (0) (by decide) cert214 m hm
#print axioms never214


/-- Third-level first-hole refinement 215, 1RB0LD_1RC1LA_0RD1LC_1LD1RB_------_------; entry 17, period 1. -/
def p215 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert215 : zipCycle p215 17 1 false (-1) = true := by decide +kernel
theorem never215 (m : Machine) (hm : compatible p215 m) : NeverHalts m :=
  zipCycle_sound p215 17 1 false (-1) (by decide) cert215 m hm
#print axioms never215


/-- Third-level first-hole refinement 216, 1RB0LD_1RC1LA_0RD1RC_1LD1RB_------_------; entry 2, period 10. -/
def p216 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert216 : zipCycle p216 2 10 true (0) = true := by decide +kernel
theorem never216 (m : Machine) (hm : compatible p216 m) : NeverHalts m :=
  zipCycle_sound p216 2 10 true (0) (by decide) cert216 m hm
#print axioms never216


/-- Third-level first-hole refinement 217, 1RB0LD_1RC1LA_0RD0LD_1LD1RB_------_------; entry 1, period 14. -/
def p217 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert217 : zipCycle p217 1 14 true (0) = true := by decide +kernel
theorem never217 (m : Machine) (hm : compatible p217 m) : NeverHalts m :=
  zipCycle_sound p217 1 14 true (0) (by decide) cert217 m hm
#print axioms never217


/-- Third-level first-hole refinement 218, 1RB0LD_1RC1LA_0RD1LD_1LD1RB_------_------; entry 5, period 6. -/
def p218 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert218 : zipCycle p218 5 6 true (0) = true := by decide +kernel
theorem never218 (m : Machine) (hm : compatible p218 m) : NeverHalts m :=
  zipCycle_sound p218 5 6 true (0) (by decide) cert218 m hm
#print axioms never218


/-- Third-level first-hole refinement 219, 1RB0LD_1RC1LA_0RD0RD_1LD1RB_------_------; entry 1, period 11. -/
def p219 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert219 : zipCycle p219 1 11 true (0) = true := by decide +kernel
theorem never219 (m : Machine) (hm : compatible p219 m) : NeverHalts m :=
  zipCycle_sound p219 1 11 true (0) (by decide) cert219 m hm
#print axioms never219


/-- Third-level first-hole refinement 220, 1RB0LD_1RC1LA_0RD1RD_1LD1RB_------_------; entry 1, period 11. -/
def p220 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert220 : zipCycle p220 1 11 true (0) = true := by decide +kernel
theorem never220 (m : Machine) (hm : compatible p220 m) : NeverHalts m :=
  zipCycle_sound p220 1 11 true (0) (by decide) cert220 m hm
#print axioms never220


/-- Third-level first-hole refinement 221, 1RB0LE_1RC1LA_0RD---_1LD1RB_---1RA_------; entry 6, period 4. -/
def p221 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert221 : zipCycle p221 6 4 true (0) = true := by decide +kernel
theorem never221 (m : Machine) (hm : compatible p221 m) : NeverHalts m :=
  zipCycle_sound p221 6 4 true (0) (by decide) cert221 m hm
#print axioms never221


/-- Third-level first-hole refinement 222, 1RB0LE_1RC1LA_0RD---_1LD1RB_---0LC_------; entry 10, period 1. -/
def p222 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert222 : zipCycle p222 10 1 false (0) = true := by decide +kernel
theorem never222 (m : Machine) (hm : compatible p222 m) : NeverHalts m :=
  zipCycle_sound p222 10 1 false (0) (by decide) cert222 m hm
#print axioms never222


/-- Third-level first-hole refinement 223, 1RB0LE_1RC1LA_0RD---_1LD1RB_---0LD_------; entry 9, period 1. -/
def p223 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert223 : zipCycle p223 9 1 false (-1) = true := by decide +kernel
theorem never223 (m : Machine) (hm : compatible p223 m) : NeverHalts m :=
  zipCycle_sound p223 9 1 false (-1) (by decide) cert223 m hm
#print axioms never223


/-- Third-level first-hole refinement 224, 1RB0LE_1RC1LA_0RD---_1LD1RB_---1LD_------; entry 9, period 1. -/
def p224 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert224 : zipCycle p224 9 1 false (-1) = true := by decide +kernel
theorem never224 (m : Machine) (hm : compatible p224 m) : NeverHalts m :=
  zipCycle_sound p224 9 1 false (-1) (by decide) cert224 m hm
#print axioms never224


/-- Third-level first-hole refinement 225, 1RB0LE_1RC1LA_0RD---_1LD1RB_---0RD_------; entry 9, period 1. -/
def p225 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert225 : zipCycle p225 9 1 false (1) = true := by decide +kernel
theorem never225 (m : Machine) (hm : compatible p225 m) : NeverHalts m :=
  zipCycle_sound p225 9 1 false (1) (by decide) cert225 m hm
#print axioms never225


/-- Third-level first-hole refinement 226, 1RB1LE_1RC1LA_0RD---_1LD1RB_---1RA_------; entry 7, period 2. -/
def p226 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert226 : zipCycle p226 7 2 true (0) = true := by decide +kernel
theorem never226 (m : Machine) (hm : compatible p226 m) : NeverHalts m :=
  zipCycle_sound p226 7 2 true (0) (by decide) cert226 m hm
#print axioms never226


/-- Third-level first-hole refinement 227, 1RB1LE_1RC1LA_0RD---_1LD1RB_---0LC_------; entry 10, period 1. -/
def p227 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert227 : zipCycle p227 10 1 false (0) = true := by decide +kernel
theorem never227 (m : Machine) (hm : compatible p227 m) : NeverHalts m :=
  zipCycle_sound p227 10 1 false (0) (by decide) cert227 m hm
#print axioms never227


/-- Third-level first-hole refinement 228, 1RB1LE_1RC1LA_0RD---_1LD1RB_---0LD_------; entry 9, period 1. -/
def p228 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert228 : zipCycle p228 9 1 false (-1) = true := by decide +kernel
theorem never228 (m : Machine) (hm : compatible p228 m) : NeverHalts m :=
  zipCycle_sound p228 9 1 false (-1) (by decide) cert228 m hm
#print axioms never228


/-- Third-level first-hole refinement 229, 1RB1LE_1RC1LA_0RD---_1LD1RB_---1LD_------; entry 9, period 1. -/
def p229 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert229 : zipCycle p229 9 1 false (-1) = true := by decide +kernel
theorem never229 (m : Machine) (hm : compatible p229 m) : NeverHalts m :=
  zipCycle_sound p229 9 1 false (-1) (by decide) cert229 m hm
#print axioms never229


/-- Third-level first-hole refinement 230, 1RB1LE_1RC1LA_0RD---_1LD1RB_---1RD_------; entry 5, period 4. -/
def p230 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert230 : zipCycle p230 5 4 true (0) = true := by decide +kernel
theorem never230 (m : Machine) (hm : compatible p230 m) : NeverHalts m :=
  zipCycle_sound p230 5 4 true (0) (by decide) cert230 m hm
#print axioms never230


/-- Third-level first-hole refinement 231, 1RB0RE_1RC1LA_0RD---_1LD1RB_---1LA_------; entry 6, period 4. -/
def p231 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert231 : zipCycle p231 6 4 true (1) = true := by decide +kernel
theorem never231 (m : Machine) (hm : compatible p231 m) : NeverHalts m :=
  zipCycle_sound p231 6 4 true (1) (by decide) cert231 m hm
#print axioms never231


/-- Third-level first-hole refinement 232, 1RB0RE_1RC1LA_0RD---_1LD1RB_---0LB_------; entry 1, period 11. -/
def p232 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert232 : zipCycle p232 1 11 true (1) = true := by decide +kernel
theorem never232 (m : Machine) (hm : compatible p232 m) : NeverHalts m :=
  zipCycle_sound p232 1 11 true (1) (by decide) cert232 m hm
#print axioms never232


/-- Third-level first-hole refinement 233, 1RB0RE_1RC1LA_0RD---_1LD1RB_---0RB_------; entry 1, period 13. -/
def p233 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert233 : zipCycle p233 1 13 true (1) = true := by decide +kernel
theorem never233 (m : Machine) (hm : compatible p233 m) : NeverHalts m :=
  zipCycle_sound p233 1 13 true (1) (by decide) cert233 m hm
#print axioms never233


/-- Third-level first-hole refinement 234, 1RB0RE_1RC1LA_0RD---_1LD1RB_---1RB_------; entry 1, period 11. -/
def p234 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert234 : zipCycle p234 1 11 true (1) = true := by decide +kernel
theorem never234 (m : Machine) (hm : compatible p234 m) : NeverHalts m :=
  zipCycle_sound p234 1 11 true (1) (by decide) cert234 m hm
#print axioms never234


/-- Third-level first-hole refinement 235, 1RB0RE_1RC1LA_0RD---_1LD1RB_---0LC_------; entry 17, period 1. -/
def p235 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert235 : zipCycle p235 17 1 false (1) = true := by decide +kernel
theorem never235 (m : Machine) (hm : compatible p235 m) : NeverHalts m :=
  zipCycle_sound p235 17 1 false (1) (by decide) cert235 m hm
#print axioms never235


/-- Third-level first-hole refinement 236, 1RB0RE_1RC1LA_0RD---_1LD1RB_---1LC_------; entry 1, period 15. -/
def p236 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert236 : zipCycle p236 1 15 true (1) = true := by decide +kernel
theorem never236 (m : Machine) (hm : compatible p236 m) : NeverHalts m :=
  zipCycle_sound p236 1 15 true (1) (by decide) cert236 m hm
#print axioms never236


/-- Third-level first-hole refinement 237, 1RB0RE_1RC1LA_0RD---_1LD1RB_---0LD_------; entry 14, period 1. -/
def p237 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert237 : zipCycle p237 14 1 false (0) = true := by decide +kernel
theorem never237 (m : Machine) (hm : compatible p237 m) : NeverHalts m :=
  zipCycle_sound p237 14 1 false (0) (by decide) cert237 m hm
#print axioms never237


/-- Third-level first-hole refinement 238, 1RB0RE_1RC1LA_0RD---_1LD1RB_---1LD_------; entry 14, period 1. -/
def p238 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert238 : zipCycle p238 14 1 false (0) = true := by decide +kernel
theorem never238 (m : Machine) (hm : compatible p238 m) : NeverHalts m :=
  zipCycle_sound p238 14 1 false (0) (by decide) cert238 m hm
#print axioms never238


/-- Third-level first-hole refinement 239, 1RB0RE_1RC1LA_0RD---_1LD1RB_---0RD_------; entry 1, period 9. -/
def p239 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert239 : zipCycle p239 1 9 true (1) = true := by decide +kernel
theorem never239 (m : Machine) (hm : compatible p239 m) : NeverHalts m :=
  zipCycle_sound p239 1 9 true (1) (by decide) cert239 m hm
#print axioms never239


/-- Third-level first-hole refinement 240, 1RB0RE_1RC1LA_0RD---_1LD1RB_---1RD_------; entry 1, period 9. -/
def p240 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert240 : zipCycle p240 1 9 true (1) = true := by decide +kernel
theorem never240 (m : Machine) (hm : compatible p240 m) : NeverHalts m :=
  zipCycle_sound p240 1 9 true (1) (by decide) cert240 m hm
#print axioms never240


/-- Third-level first-hole refinement 241, 1RB1RE_1RC1LA_0RD---_1LD1RB_---1LA_------; entry 7, period 2. -/
def p241 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert241 : zipCycle p241 7 2 true (1) = true := by decide +kernel
theorem never241 (m : Machine) (hm : compatible p241 m) : NeverHalts m :=
  zipCycle_sound p241 7 2 true (1) (by decide) cert241 m hm
#print axioms never241


/-- Third-level first-hole refinement 242, 1RB1RE_1RC1LA_0RD---_1LD1RB_---0LB_------; entry 9, period 5. -/
def p242 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert242 : zipCycle p242 9 5 false (1) = true := by decide +kernel
theorem never242 (m : Machine) (hm : compatible p242 m) : NeverHalts m :=
  zipCycle_sound p242 9 5 false (1) (by decide) cert242 m hm
#print axioms never242


/-- Third-level first-hole refinement 243, 1RB1RE_1RC1LA_0RD---_1LD1RB_---1LB_------; entry 9, period 5. -/
def p243 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert243 : zipCycle p243 9 5 false (1) = true := by decide +kernel
theorem never243 (m : Machine) (hm : compatible p243 m) : NeverHalts m :=
  zipCycle_sound p243 9 5 false (1) (by decide) cert243 m hm
#print axioms never243


/-- Third-level first-hole refinement 244, 1RB1RE_1RC1LA_0RD---_1LD1RB_---0RB_------; entry 1, period 13. -/
def p244 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert244 : zipCycle p244 1 13 true (1) = true := by decide +kernel
theorem never244 (m : Machine) (hm : compatible p244 m) : NeverHalts m :=
  zipCycle_sound p244 1 13 true (1) (by decide) cert244 m hm
#print axioms never244


/-- Third-level first-hole refinement 245, 1RB1RE_1RC1LA_0RD---_1LD1RB_---1RB_------; entry 1, period 11. -/
def p245 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert245 : zipCycle p245 1 11 true (1) = true := by decide +kernel
theorem never245 (m : Machine) (hm : compatible p245 m) : NeverHalts m :=
  zipCycle_sound p245 1 11 true (1) (by decide) cert245 m hm
#print axioms never245


/-- Third-level first-hole refinement 246, 1RB1RE_1RC1LA_0RD---_1LD1RB_---1LD_------; entry 5, period 4. -/
def p246 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert246 : zipCycle p246 5 4 true (1) = true := by decide +kernel
theorem never246 (m : Machine) (hm : compatible p246 m) : NeverHalts m :=
  zipCycle_sound p246 5 4 true (1) (by decide) cert246 m hm
#print axioms never246


/-- Third-level first-hole refinement 247, 1RB1RE_1RC1LA_0RD---_1LD1RB_---0RD_------; entry 1, period 9. -/
def p247 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert247 : zipCycle p247 1 9 true (1) = true := by decide +kernel
theorem never247 (m : Machine) (hm : compatible p247 m) : NeverHalts m :=
  zipCycle_sound p247 1 9 true (1) (by decide) cert247 m hm
#print axioms never247


/-- Third-level first-hole refinement 248, 1RB1RE_1RC1LA_0RD---_1LD1RB_---1RD_------; entry 1, period 9. -/
def p248 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert248 : zipCycle p248 1 9 true (1) = true := by decide +kernel
theorem never248 (m : Machine) (hm : compatible p248 m) : NeverHalts m :=
  zipCycle_sound p248 1 9 true (1) (by decide) cert248 m hm
#print axioms never248


/-- Third-level first-hole refinement 249, 1RB1LB_1RC0RA_0RD0LA_1LD1RB_------_------; entry 17, period 3. -/
def p249 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert249 : zipCycle p249 17 3 false (1) = true := by decide +kernel
theorem never249 (m : Machine) (hm : compatible p249 m) : NeverHalts m :=
  zipCycle_sound p249 17 3 false (1) (by decide) cert249 m hm
#print axioms never249


/-- Third-level first-hole refinement 250, 1RB1LB_1RC0RA_0RD1LA_1LD1RB_------_------; entry 17, period 3. -/
def p250 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert250 : zipCycle p250 17 3 false (1) = true := by decide +kernel
theorem never250 (m : Machine) (hm : compatible p250 m) : NeverHalts m :=
  zipCycle_sound p250 17 3 false (1) (by decide) cert250 m hm
#print axioms never250


/-- Third-level first-hole refinement 251, 1RB1LB_1RC0RA_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p251 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert251 : zipCycle p251 0 10 true (0) = true := by decide +kernel
theorem never251 (m : Machine) (hm : compatible p251 m) : NeverHalts m :=
  zipCycle_sound p251 0 10 true (0) (by decide) cert251 m hm
#print axioms never251


/-- Third-level first-hole refinement 252, 1RB1LB_1RC0RA_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p252 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert252 : zipCycle p252 0 10 true (0) = true := by decide +kernel
theorem never252 (m : Machine) (hm : compatible p252 m) : NeverHalts m :=
  zipCycle_sound p252 0 10 true (0) (by decide) cert252 m hm
#print axioms never252


/-- Third-level first-hole refinement 253, 1RB1LB_1RC0RA_0RD0LB_1LD1RB_------_------; entry 0, period 11. -/
def p253 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert253 : zipCycle p253 0 11 true (0) = true := by decide +kernel
theorem never253 (m : Machine) (hm : compatible p253 m) : NeverHalts m :=
  zipCycle_sound p253 0 11 true (0) (by decide) cert253 m hm
#print axioms never253


/-- Third-level first-hole refinement 254, 1RB1LB_1RC0RA_0RD1LB_1LD1RB_------_------; entry 6, period 4. -/
def p254 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert254 : zipCycle p254 6 4 true (2) = true := by decide +kernel
theorem never254 (m : Machine) (hm : compatible p254 m) : NeverHalts m :=
  zipCycle_sound p254 6 4 true (2) (by decide) cert254 m hm
#print axioms never254


/-- Third-level first-hole refinement 255, 1RB1LB_1RC0RA_0RD0RB_1LD1RB_------_------; entry 1, period 9. -/
def p255 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert255 : zipCycle p255 1 9 true (1) = true := by decide +kernel
theorem never255 (m : Machine) (hm : compatible p255 m) : NeverHalts m :=
  zipCycle_sound p255 1 9 true (1) (by decide) cert255 m hm
#print axioms never255


/-- Third-level first-hole refinement 256, 1RB1LB_1RC0RA_0RD1RB_1LD1RB_------_------; entry 1, period 9. -/
def p256 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert256 : zipCycle p256 1 9 true (1) = true := by decide +kernel
theorem never256 (m : Machine) (hm : compatible p256 m) : NeverHalts m :=
  zipCycle_sound p256 1 9 true (1) (by decide) cert256 m hm
#print axioms never256


/-- Third-level first-hole refinement 257, 1RB1LB_1RC0RA_0RD0LC_1LD1RB_------_------; entry 14, period 1. -/
def p257 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert257 : zipCycle p257 14 1 false (0) = true := by decide +kernel
theorem never257 (m : Machine) (hm : compatible p257 m) : NeverHalts m :=
  zipCycle_sound p257 14 1 false (0) (by decide) cert257 m hm
#print axioms never257


/-- Third-level first-hole refinement 258, 1RB1LB_1RC0RA_0RD1LC_1LD1RB_------_------; entry 10, period 8. -/
def p258 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert258 : zipCycle p258 10 8 true (-1) = true := by decide +kernel
theorem never258 (m : Machine) (hm : compatible p258 m) : NeverHalts m :=
  zipCycle_sound p258 10 8 true (-1) (by decide) cert258 m hm
#print axioms never258


/-- Third-level first-hole refinement 259, 1RB1LB_1RC0RA_0RD1RC_1LD1RB_------_------; entry 2, period 8. -/
def p259 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert259 : zipCycle p259 2 8 true (1) = true := by decide +kernel
theorem never259 (m : Machine) (hm : compatible p259 m) : NeverHalts m :=
  zipCycle_sound p259 2 8 true (1) (by decide) cert259 m hm
#print axioms never259


/-- Third-level first-hole refinement 260, 1RB1LB_1RC0RA_0RD0LD_1LD1RB_------_------; entry 1, period 10. -/
def p260 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert260 : zipCycle p260 1 10 true (1) = true := by decide +kernel
theorem never260 (m : Machine) (hm : compatible p260 m) : NeverHalts m :=
  zipCycle_sound p260 1 10 true (1) (by decide) cert260 m hm
#print axioms never260


/-- Third-level first-hole refinement 261, 1RB1LB_1RC0RA_0RD1LD_1LD1RB_------_------; entry 0, period 12. -/
def p261 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert261 : zipCycle p261 0 12 true (0) = true := by decide +kernel
theorem never261 (m : Machine) (hm : compatible p261 m) : NeverHalts m :=
  zipCycle_sound p261 0 12 true (0) (by decide) cert261 m hm
#print axioms never261


/-- Third-level first-hole refinement 262, 1RB1LB_1RC0RA_0RD0RD_1LD1RB_------_------; entry 3, period 7. -/
def p262 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert262 : zipCycle p262 3 7 true (1) = true := by decide +kernel
theorem never262 (m : Machine) (hm : compatible p262 m) : NeverHalts m :=
  zipCycle_sound p262 3 7 true (1) (by decide) cert262 m hm
#print axioms never262


/-- Third-level first-hole refinement 263, 1RB1LB_1RC0RA_0RD1RD_1LD1RB_------_------; entry 0, period 13. -/
def p263 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert263 : zipCycle p263 0 13 true (0) = true := by decide +kernel
theorem never263 (m : Machine) (hm : compatible p263 m) : NeverHalts m :=
  zipCycle_sound p263 0 13 true (0) (by decide) cert263 m hm
#print axioms never263


/-- Third-level first-hole refinement 264, 1RB0RC_1RC0RA_0RD0LA_1LD1RB_------_------; entry 0, period 29. -/
def p264 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert264 : zipCycle p264 0 29 true (0) = true := by decide +kernel
theorem never264 (m : Machine) (hm : compatible p264 m) : NeverHalts m :=
  zipCycle_sound p264 0 29 true (0) (by decide) cert264 m hm
#print axioms never264


/-- Third-level first-hole refinement 265, 1RB0RC_1RC0RA_0RD1LA_1LD1RB_------_------; entry 6, period 12. -/
def p265 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert265 : zipCycle p265 6 12 true (1) = true := by decide +kernel
theorem never265 (m : Machine) (hm : compatible p265 m) : NeverHalts m :=
  zipCycle_sound p265 6 12 true (1) (by decide) cert265 m hm
#print axioms never265


/-- Third-level first-hole refinement 266, 1RB0RC_1RC0RA_0RD1RA_1LD1RB_------_------; entry 0, period 26. -/
def p266 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert266 : zipCycle p266 0 26 true (0) = true := by decide +kernel
theorem never266 (m : Machine) (hm : compatible p266 m) : NeverHalts m :=
  zipCycle_sound p266 0 26 true (0) (by decide) cert266 m hm
#print axioms never266


/-- Third-level first-hole refinement 267, 1RB0RC_1RC0RA_0RD0LB_1LD1RB_------_------; entry 1, period 19. -/
def p267 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert267 : zipCycle p267 1 19 true (1) = true := by decide +kernel
theorem never267 (m : Machine) (hm : compatible p267 m) : NeverHalts m :=
  zipCycle_sound p267 1 19 true (1) (by decide) cert267 m hm
#print axioms never267


/-- Third-level first-hole refinement 268, 1RB0RC_1RC0RA_0RD0RB_1LD1RB_------_------; entry 0, period 18. -/
def p268 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert268 : zipCycle p268 0 18 true (0) = true := by decide +kernel
theorem never268 (m : Machine) (hm : compatible p268 m) : NeverHalts m :=
  zipCycle_sound p268 0 18 true (0) (by decide) cert268 m hm
#print axioms never268


/-- Third-level first-hole refinement 269, 1RB0RC_1RC0RA_0RD1RB_1LD1RB_------_------; entry 0, period 18. -/
def p269 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert269 : zipCycle p269 0 18 true (0) = true := by decide +kernel
theorem never269 (m : Machine) (hm : compatible p269 m) : NeverHalts m :=
  zipCycle_sound p269 0 18 true (0) (by decide) cert269 m hm
#print axioms never269


/-- Third-level first-hole refinement 270, 1RB0RC_1RC0RA_0RD0LC_1LD1RB_------_------; entry 10, period 8. -/
def p270 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert270 : zipCycle p270 10 8 true (1) = true := by decide +kernel
theorem never270 (m : Machine) (hm : compatible p270 m) : NeverHalts m :=
  zipCycle_sound p270 10 8 true (1) (by decide) cert270 m hm
#print axioms never270


/-- Third-level first-hole refinement 271, 1RB0RC_1RC0RA_0RD1LC_1LD1RB_------_------; entry 0, period 20. -/
def p271 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert271 : zipCycle p271 0 20 true (0) = true := by decide +kernel
theorem never271 (m : Machine) (hm : compatible p271 m) : NeverHalts m :=
  zipCycle_sound p271 0 20 true (0) (by decide) cert271 m hm
#print axioms never271


/-- Third-level first-hole refinement 272, 1RB0RC_1RC0RA_0RD1RC_1LD1RB_------_------; entry 2, period 16. -/
def p272 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert272 : zipCycle p272 2 16 true (1) = true := by decide +kernel
theorem never272 (m : Machine) (hm : compatible p272 m) : NeverHalts m :=
  zipCycle_sound p272 2 16 true (1) (by decide) cert272 m hm
#print axioms never272


/-- Third-level first-hole refinement 273, 1RB0RC_1RC0RA_0RD0LD_1LD1RB_------_------; entry 1, period 23. -/
def p273 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert273 : zipCycle p273 1 23 true (1) = true := by decide +kernel
theorem never273 (m : Machine) (hm : compatible p273 m) : NeverHalts m :=
  zipCycle_sound p273 1 23 true (1) (by decide) cert273 m hm
#print axioms never273


/-- Third-level first-hole refinement 274, 1RB0RC_1RC0RA_0RD1LD_1LD1RB_------_------; entry 11, period 6. -/
def p274 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert274 : zipCycle p274 11 6 true (1) = true := by decide +kernel
theorem never274 (m : Machine) (hm : compatible p274 m) : NeverHalts m :=
  zipCycle_sound p274 11 6 true (1) (by decide) cert274 m hm
#print axioms never274


/-- Third-level first-hole refinement 275, 1RB0RC_1RC0RA_0RD0RD_1LD1RB_------_------; entry 1, period 17. -/
def p275 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert275 : zipCycle p275 1 17 true (1) = true := by decide +kernel
theorem never275 (m : Machine) (hm : compatible p275 m) : NeverHalts m :=
  zipCycle_sound p275 1 17 true (1) (by decide) cert275 m hm
#print axioms never275


/-- Third-level first-hole refinement 276, 1RB0RC_1RC0RA_0RD1RD_1LD1RB_------_------; entry 1, period 17. -/
def p276 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert276 : zipCycle p276 1 17 true (1) = true := by decide +kernel
theorem never276 (m : Machine) (hm : compatible p276 m) : NeverHalts m :=
  zipCycle_sound p276 1 17 true (1) (by decide) cert276 m hm
#print axioms never276


/-- Third-level first-hole refinement 277, 1RB0LE_1RC0RA_0RD---_1LD1RB_0RA---_------; entry 0, period 9. -/
def p277 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert277 : zipCycle p277 0 9 true (0) = true := by decide +kernel
theorem never277 (m : Machine) (hm : compatible p277 m) : NeverHalts m :=
  zipCycle_sound p277 0 9 true (0) (by decide) cert277 m hm
#print axioms never277


/-- Third-level first-hole refinement 278, 1RB0LE_1RC0RA_0RD---_1LD1RB_1RA---_------; entry 0, period 9. -/
def p278 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert278 : zipCycle p278 0 9 true (0) = true := by decide +kernel
theorem never278 (m : Machine) (hm : compatible p278 m) : NeverHalts m :=
  zipCycle_sound p278 0 9 true (0) (by decide) cert278 m hm
#print axioms never278


/-- Third-level first-hole refinement 279, 1RB0LE_1RC0RA_0RD---_1LD1RB_0LB---_------; entry 0, period 10. -/
def p279 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert279 : zipCycle p279 0 10 true (0) = true := by decide +kernel
theorem never279 (m : Machine) (hm : compatible p279 m) : NeverHalts m :=
  zipCycle_sound p279 0 10 true (0) (by decide) cert279 m hm
#print axioms never279


/-- Third-level first-hole refinement 280, 1RB0LE_1RC0RA_0RD---_1LD1RB_0RB---_------; entry 1, period 8. -/
def p280 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert280 : zipCycle p280 1 8 true (1) = true := by decide +kernel
theorem never280 (m : Machine) (hm : compatible p280 m) : NeverHalts m :=
  zipCycle_sound p280 1 8 true (1) (by decide) cert280 m hm
#print axioms never280


/-- Third-level first-hole refinement 281, 1RB0LE_1RC0RA_0RD---_1LD1RB_1RB---_------; entry 1, period 8. -/
def p281 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert281 : zipCycle p281 1 8 true (1) = true := by decide +kernel
theorem never281 (m : Machine) (hm : compatible p281 m) : NeverHalts m :=
  zipCycle_sound p281 1 8 true (1) (by decide) cert281 m hm
#print axioms never281


/-- Third-level first-hole refinement 282, 1RB0LE_1RC0RA_0RD---_1LD1RB_0RC---_------; entry 1, period 18. -/
def p282 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert282 : zipCycle p282 1 18 true (1) = true := by decide +kernel
theorem never282 (m : Machine) (hm : compatible p282 m) : NeverHalts m :=
  zipCycle_sound p282 1 18 true (1) (by decide) cert282 m hm
#print axioms never282


/-- Third-level first-hole refinement 283, 1RB0LE_1RC0RA_0RD---_1LD1RB_1RC---_------; entry 2, period 7. -/
def p283 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert283 : zipCycle p283 2 7 true (1) = true := by decide +kernel
theorem never283 (m : Machine) (hm : compatible p283 m) : NeverHalts m :=
  zipCycle_sound p283 2 7 true (1) (by decide) cert283 m hm
#print axioms never283


/-- Third-level first-hole refinement 284, 1RB0LE_1RC0RA_0RD---_1LD1RB_0LD---_------; entry 1, period 9. -/
def p284 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert284 : zipCycle p284 1 9 true (1) = true := by decide +kernel
theorem never284 (m : Machine) (hm : compatible p284 m) : NeverHalts m :=
  zipCycle_sound p284 1 9 true (1) (by decide) cert284 m hm
#print axioms never284


/-- Third-level first-hole refinement 285, 1RB0LE_1RC0RA_0RD---_1LD1RB_1LD---_------; entry 0, period 11. -/
def p285 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert285 : zipCycle p285 0 11 true (0) = true := by decide +kernel
theorem never285 (m : Machine) (hm : compatible p285 m) : NeverHalts m :=
  zipCycle_sound p285 0 11 true (0) (by decide) cert285 m hm
#print axioms never285


/-- Third-level first-hole refinement 286, 1RB0LE_1RC0RA_0RD---_1LD1RB_0RD---_------; entry 3, period 6. -/
def p286 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert286 : zipCycle p286 3 6 true (1) = true := by decide +kernel
theorem never286 (m : Machine) (hm : compatible p286 m) : NeverHalts m :=
  zipCycle_sound p286 3 6 true (1) (by decide) cert286 m hm
#print axioms never286


/-- Third-level first-hole refinement 287, 1RB0LE_1RC0RA_0RD---_1LD1RB_1RD---_------; entry 0, period 12. -/
def p287 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert287 : zipCycle p287 0 12 true (0) = true := by decide +kernel
theorem never287 (m : Machine) (hm : compatible p287 m) : NeverHalts m :=
  zipCycle_sound p287 0 12 true (0) (by decide) cert287 m hm
#print axioms never287


/-- Third-level first-hole refinement 288, 1RB0LE_1RC0RA_0RD---_1LD1RB_0RE---_------; entry 8, period 1. -/
def p288 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert288 : zipCycle p288 8 1 true (2) = true := by decide +kernel
theorem never288 (m : Machine) (hm : compatible p288 m) : NeverHalts m :=
  zipCycle_sound p288 8 1 true (2) (by decide) cert288 m hm
#print axioms never288


/-- Third-level first-hole refinement 289, 1RB0LE_1RC0RA_0RD---_1LD1RB_1RE---_------; entry 8, period 1. -/
def p289 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert289 : zipCycle p289 8 1 true (2) = true := by decide +kernel
theorem never289 (m : Machine) (hm : compatible p289 m) : NeverHalts m :=
  zipCycle_sound p289 8 1 true (2) (by decide) cert289 m hm
#print axioms never289


/-- Third-level first-hole refinement 290, 1RB1LE_1RC0RA_0RD---_1LD1RB_0RA---_------; entry 7, period 2. -/
def p290 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert290 : zipCycle p290 7 2 true (2) = true := by decide +kernel
theorem never290 (m : Machine) (hm : compatible p290 m) : NeverHalts m :=
  zipCycle_sound p290 7 2 true (2) (by decide) cert290 m hm
#print axioms never290


/-- Third-level first-hole refinement 291, 1RB1LE_1RC0RA_0RD---_1LD1RB_0LB---_------; entry 0, period 12. -/
def p291 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert291 : zipCycle p291 0 12 true (0) = true := by decide +kernel
theorem never291 (m : Machine) (hm : compatible p291 m) : NeverHalts m :=
  zipCycle_sound p291 0 12 true (0) (by decide) cert291 m hm
#print axioms never291


/-- Third-level first-hole refinement 292, 1RB1LE_1RC0RA_0RD---_1LD1RB_0RB---_------; entry 0, period 10. -/
def p292 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert292 : zipCycle p292 0 10 true (0) = true := by decide +kernel
theorem never292 (m : Machine) (hm : compatible p292 m) : NeverHalts m :=
  zipCycle_sound p292 0 10 true (0) (by decide) cert292 m hm
#print axioms never292


/-- Third-level first-hole refinement 293, 1RB1LE_1RC0RA_0RD---_1LD1RB_1RB---_------; entry 0, period 10. -/
def p293 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert293 : zipCycle p293 0 10 true (0) = true := by decide +kernel
theorem never293 (m : Machine) (hm : compatible p293 m) : NeverHalts m :=
  zipCycle_sound p293 0 10 true (0) (by decide) cert293 m hm
#print axioms never293


/-- Third-level first-hole refinement 294, 1RB1LE_1RC0RA_0RD---_1LD1RB_1LD---_------; entry 5, period 4. -/
def p294 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert294 : zipCycle p294 5 4 true (1) = true := by decide +kernel
theorem never294 (m : Machine) (hm : compatible p294 m) : NeverHalts m :=
  zipCycle_sound p294 5 4 true (1) (by decide) cert294 m hm
#print axioms never294


/-- Third-level first-hole refinement 295, 1RB1LE_1RC0RA_0RD---_1LD1RB_0RD---_------; entry 1, period 9. -/
def p295 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert295 : zipCycle p295 1 9 true (1) = true := by decide +kernel
theorem never295 (m : Machine) (hm : compatible p295 m) : NeverHalts m :=
  zipCycle_sound p295 1 9 true (1) (by decide) cert295 m hm
#print axioms never295


/-- Third-level first-hole refinement 296, 1RB1LE_1RC0RA_0RD---_1LD1RB_1RD---_------; entry 1, period 9. -/
def p296 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert296 : zipCycle p296 1 9 true (1) = true := by decide +kernel
theorem never296 (m : Machine) (hm : compatible p296 m) : NeverHalts m :=
  zipCycle_sound p296 1 9 true (1) (by decide) cert296 m hm
#print axioms never296


/-- Third-level first-hole refinement 297, 1RB0RE_1RC0RA_0RD---_1LD1RB_0LA---_------; entry 0, period 9. -/
def p297 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert297 : zipCycle p297 0 9 true (0) = true := by decide +kernel
theorem never297 (m : Machine) (hm : compatible p297 m) : NeverHalts m :=
  zipCycle_sound p297 0 9 true (0) (by decide) cert297 m hm
#print axioms never297


/-- Third-level first-hole refinement 298, 1RB0RE_1RC0RA_0RD---_1LD1RB_1LA---_------; entry 0, period 11. -/
def p298 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert298 : zipCycle p298 0 11 true (0) = true := by decide +kernel
theorem never298 (m : Machine) (hm : compatible p298 m) : NeverHalts m :=
  zipCycle_sound p298 0 11 true (0) (by decide) cert298 m hm
#print axioms never298


/-- Third-level first-hole refinement 299, 1RB0RE_1RC0RA_0RD---_1LD1RB_0RA---_------; entry 0, period 9. -/
def p299 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert299 : zipCycle p299 0 9 true (0) = true := by decide +kernel
theorem never299 (m : Machine) (hm : compatible p299 m) : NeverHalts m :=
  zipCycle_sound p299 0 9 true (0) (by decide) cert299 m hm
#print axioms never299

end BB6.Agent24Raw45D3_02
