import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_12
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1200, 1RB---_1RC1LE_0RD---_1LD1RB_1LA0LE_------; entry 8, period 4. -/
def p1200 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1200 : zipCycle p1200 8 4 false (0) = true := by decide +kernel
theorem never1200 (m : Machine) (hm : compatible p1200 m) : NeverHalts m :=
  zipCycle_sound p1200 8 4 false (0) (by decide) cert1200 m hm
#print axioms never1200


/-- Third-level first-hole refinement 1201, 1RB---_1RC1LE_0RD---_1LD1RB_0LB0LE_------; entry 8, period 8. -/
def p1201 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1201 : zipCycle p1201 8 8 false (0) = true := by decide +kernel
theorem never1201 (m : Machine) (hm : compatible p1201 m) : NeverHalts m :=
  zipCycle_sound p1201 8 8 false (0) (by decide) cert1201 m hm
#print axioms never1201


/-- Third-level first-hole refinement 1202, 1RB---_1RC1LE_0RD---_1LD1RB_0LC0LE_------; entry 11, period 1. -/
def p1202 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1202 : zipCycle p1202 11 1 false (-1) = true := by decide +kernel
theorem never1202 (m : Machine) (hm : compatible p1202 m) : NeverHalts m :=
  zipCycle_sound p1202 11 1 false (-1) (by decide) cert1202 m hm
#print axioms never1202


/-- Third-level first-hole refinement 1203, 1RB---_1RC1LE_0RD---_1LD1RB_0RC0LE_------; entry 11, period 1. -/
def p1203 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1203 : zipCycle p1203 11 1 false (1) = true := by decide +kernel
theorem never1203 (m : Machine) (hm : compatible p1203 m) : NeverHalts m :=
  zipCycle_sound p1203 11 1 false (1) (by decide) cert1203 m hm
#print axioms never1203


/-- Third-level first-hole refinement 1204, 1RB---_1RC1LE_0RD---_1LD1RB_0LD0LE_------; entry 10, period 1. -/
def p1204 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1204 : zipCycle p1204 10 1 false (-2) = true := by decide +kernel
theorem never1204 (m : Machine) (hm : compatible p1204 m) : NeverHalts m :=
  zipCycle_sound p1204 10 1 false (-2) (by decide) cert1204 m hm
#print axioms never1204


/-- Third-level first-hole refinement 1205, 1RB---_1RC1LE_0RD---_1LD1RB_1LD0LE_------; entry 10, period 1. -/
def p1205 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1205 : zipCycle p1205 10 1 false (-2) = true := by decide +kernel
theorem never1205 (m : Machine) (hm : compatible p1205 m) : NeverHalts m :=
  zipCycle_sound p1205 10 1 false (-2) (by decide) cert1205 m hm
#print axioms never1205


/-- Third-level first-hole refinement 1206, 1RB---_1RC1LE_0RD---_1LD1RB_0RD0LE_------; entry 10, period 1. -/
def p1206 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1206 : zipCycle p1206 10 1 false (0) = true := by decide +kernel
theorem never1206 (m : Machine) (hm : compatible p1206 m) : NeverHalts m :=
  zipCycle_sound p1206 10 1 false (0) (by decide) cert1206 m hm
#print axioms never1206


/-- Third-level first-hole refinement 1207, 1RB---_1RC1LE_0RD---_1LD1RB_1RD0LE_------; entry 8, period 5. -/
def p1207 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1207 : zipCycle p1207 8 5 false (0) = true := by decide +kernel
theorem never1207 (m : Machine) (hm : compatible p1207 m) : NeverHalts m :=
  zipCycle_sound p1207 8 5 false (0) (by decide) cert1207 m hm
#print axioms never1207


/-- Third-level first-hole refinement 1208, 1RB---_1RC1LE_0RD---_1LD1RB_0LE0LE_------; entry 9, period 1. -/
def p1208 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1208 : zipCycle p1208 9 1 false (-1) = true := by decide +kernel
theorem never1208 (m : Machine) (hm : compatible p1208 m) : NeverHalts m :=
  zipCycle_sound p1208 9 1 false (-1) (by decide) cert1208 m hm
#print axioms never1208


/-- Third-level first-hole refinement 1209, 1RB---_1RC1LE_0RD---_1LD1RB_1LE0LE_------; entry 9, period 1. -/
def p1209 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1209 : zipCycle p1209 9 1 false (-1) = true := by decide +kernel
theorem never1209 (m : Machine) (hm : compatible p1209 m) : NeverHalts m :=
  zipCycle_sound p1209 9 1 false (-1) (by decide) cert1209 m hm
#print axioms never1209


/-- Third-level first-hole refinement 1210, 1RB---_1RC1LE_0RD---_1LD1RB_0RE0LE_------; entry 16, period 1. -/
def p1210 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1210 : zipCycle p1210 16 1 true (2) = true := by decide +kernel
theorem never1210 (m : Machine) (hm : compatible p1210 m) : NeverHalts m :=
  zipCycle_sound p1210 16 1 true (2) (by decide) cert1210 m hm
#print axioms never1210


/-- Third-level first-hole refinement 1211, 1RB---_1RC1LE_0RD---_1LD1RB_1RE0LE_------; entry 27, period 1. -/
def p1211 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1211 : zipCycle p1211 27 1 true (-3) = true := by decide +kernel
theorem never1211 (m : Machine) (hm : compatible p1211 m) : NeverHalts m :=
  zipCycle_sound p1211 27 1 true (-3) (by decide) cert1211 m hm
#print axioms never1211


/-- Third-level first-hole refinement 1212, 1RB---_1RC1LE_0RD---_1LD1RB_1LA1LE_------; entry 8, period 4. -/
def p1212 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1212 : zipCycle p1212 8 4 false (0) = true := by decide +kernel
theorem never1212 (m : Machine) (hm : compatible p1212 m) : NeverHalts m :=
  zipCycle_sound p1212 8 4 false (0) (by decide) cert1212 m hm
#print axioms never1212


/-- Third-level first-hole refinement 1213, 1RB---_1RC1LE_0RD---_1LD1RB_0RB1LE_------; entry 9, period 2. -/
def p1213 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1213 : zipCycle p1213 9 2 true (-1) = true := by decide +kernel
theorem never1213 (m : Machine) (hm : compatible p1213 m) : NeverHalts m :=
  zipCycle_sound p1213 9 2 true (-1) (by decide) cert1213 m hm
#print axioms never1213


/-- Third-level first-hole refinement 1214, 1RB---_1RC1LE_0RD---_1LD1RB_1RB1LE_------; entry 8, period 3. -/
def p1214 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1214 : zipCycle p1214 8 3 false (0) = true := by decide +kernel
theorem never1214 (m : Machine) (hm : compatible p1214 m) : NeverHalts m :=
  zipCycle_sound p1214 8 3 false (0) (by decide) cert1214 m hm
#print axioms never1214


/-- Third-level first-hole refinement 1215, 1RB---_1RC1LE_0RD---_1LD1RB_0LC1LE_------; entry 11, period 1. -/
def p1215 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1215 : zipCycle p1215 11 1 false (-1) = true := by decide +kernel
theorem never1215 (m : Machine) (hm : compatible p1215 m) : NeverHalts m :=
  zipCycle_sound p1215 11 1 false (-1) (by decide) cert1215 m hm
#print axioms never1215


/-- Third-level first-hole refinement 1216, 1RB---_1RC1LE_0RD---_1LD1RB_1LC1LE_------; entry 8, period 5. -/
def p1216 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1216 : zipCycle p1216 8 5 false (0) = true := by decide +kernel
theorem never1216 (m : Machine) (hm : compatible p1216 m) : NeverHalts m :=
  zipCycle_sound p1216 8 5 false (0) (by decide) cert1216 m hm
#print axioms never1216


/-- Third-level first-hole refinement 1217, 1RB---_1RC1LE_0RD---_1LD1RB_0LD1LE_------; entry 10, period 1. -/
def p1217 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1217 : zipCycle p1217 10 1 false (-2) = true := by decide +kernel
theorem never1217 (m : Machine) (hm : compatible p1217 m) : NeverHalts m :=
  zipCycle_sound p1217 10 1 false (-2) (by decide) cert1217 m hm
#print axioms never1217


/-- Third-level first-hole refinement 1218, 1RB---_1RC1LE_0RD---_1LD1RB_1LD1LE_------; entry 10, period 1. -/
def p1218 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1218 : zipCycle p1218 10 1 false (-2) = true := by decide +kernel
theorem never1218 (m : Machine) (hm : compatible p1218 m) : NeverHalts m :=
  zipCycle_sound p1218 10 1 false (-2) (by decide) cert1218 m hm
#print axioms never1218


/-- Third-level first-hole refinement 1219, 1RB---_1RC1LE_0RD---_1LD1RB_0RD1LE_------; entry 8, period 4. -/
def p1219 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1219 : zipCycle p1219 8 4 true (-1) = true := by decide +kernel
theorem never1219 (m : Machine) (hm : compatible p1219 m) : NeverHalts m :=
  zipCycle_sound p1219 8 4 true (-1) (by decide) cert1219 m hm
#print axioms never1219


/-- Third-level first-hole refinement 1220, 1RB---_1RC1LE_0RD---_1LD1RB_1RD1LE_------; entry 5, period 5. -/
def p1220 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1220 : zipCycle p1220 5 5 false (2) = true := by decide +kernel
theorem never1220 (m : Machine) (hm : compatible p1220 m) : NeverHalts m :=
  zipCycle_sound p1220 5 5 false (2) (by decide) cert1220 m hm
#print axioms never1220


/-- Third-level first-hole refinement 1221, 1RB---_1RC1LE_0RD---_1LD1RB_0LE1LE_------; entry 9, period 1. -/
def p1221 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1221 : zipCycle p1221 9 1 false (-1) = true := by decide +kernel
theorem never1221 (m : Machine) (hm : compatible p1221 m) : NeverHalts m :=
  zipCycle_sound p1221 9 1 false (-1) (by decide) cert1221 m hm
#print axioms never1221


/-- Third-level first-hole refinement 1222, 1RB---_1RC1LE_0RD---_1LD1RB_1LE1LE_------; entry 9, period 1. -/
def p1222 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1222 : zipCycle p1222 9 1 false (-1) = true := by decide +kernel
theorem never1222 (m : Machine) (hm : compatible p1222 m) : NeverHalts m :=
  zipCycle_sound p1222 9 1 false (-1) (by decide) cert1222 m hm
#print axioms never1222


/-- Third-level first-hole refinement 1223, 1RB---_1RC1LE_0RD---_1LD1RB_0RE1LE_------; entry 8, period 2. -/
def p1223 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1223 : zipCycle p1223 8 2 true (-1) = true := by decide +kernel
theorem never1223 (m : Machine) (hm : compatible p1223 m) : NeverHalts m :=
  zipCycle_sound p1223 8 2 true (-1) (by decide) cert1223 m hm
#print axioms never1223


/-- Third-level first-hole refinement 1224, 1RB---_1RC1LE_0RD---_1LD1RB_1RE1LE_------; entry 7, period 3. -/
def p1224 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1224 : zipCycle p1224 7 3 false (1) = true := by decide +kernel
theorem never1224 (m : Machine) (hm : compatible p1224 m) : NeverHalts m :=
  zipCycle_sound p1224 7 3 false (1) (by decide) cert1224 m hm
#print axioms never1224


/-- Third-level first-hole refinement 1225, 1RB---_1RC1LE_0RD---_1LD1RB_0LA0RE_------; entry 0, period 11. -/
def p1225 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1225 : zipCycle p1225 0 11 true (0) = true := by decide +kernel
theorem never1225 (m : Machine) (hm : compatible p1225 m) : NeverHalts m :=
  zipCycle_sound p1225 0 11 true (0) (by decide) cert1225 m hm
#print axioms never1225


/-- Third-level first-hole refinement 1226, 1RB---_1RC1LE_0RD---_1LD1RB_1LA0RE_------; entry 8, period 5. -/
def p1226 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1226 : zipCycle p1226 8 5 true (2) = true := by decide +kernel
theorem never1226 (m : Machine) (hm : compatible p1226 m) : NeverHalts m :=
  zipCycle_sound p1226 8 5 true (2) (by decide) cert1226 m hm
#print axioms never1226


/-- Third-level first-hole refinement 1227, 1RB---_1RC1LE_0RD---_1LD1RB_0RA0RE_------; entry 0, period 11. -/
def p1227 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1227 : zipCycle p1227 0 11 true (0) = true := by decide +kernel
theorem never1227 (m : Machine) (hm : compatible p1227 m) : NeverHalts m :=
  zipCycle_sound p1227 0 11 true (0) (by decide) cert1227 m hm
#print axioms never1227


/-- Third-level first-hole refinement 1228, 1RB---_1RC1LE_0RD---_1LD1RB_1RA0RE_------; entry 0, period 11. -/
def p1228 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1228 : zipCycle p1228 0 11 true (0) = true := by decide +kernel
theorem never1228 (m : Machine) (hm : compatible p1228 m) : NeverHalts m :=
  zipCycle_sound p1228 0 11 true (0) (by decide) cert1228 m hm
#print axioms never1228


/-- Third-level first-hole refinement 1229, 1RB---_1RC1LE_0RD---_1LD1RB_0LB0RE_------; entry 1, period 10. -/
def p1229 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1229 : zipCycle p1229 1 10 true (1) = true := by decide +kernel
theorem never1229 (m : Machine) (hm : compatible p1229 m) : NeverHalts m :=
  zipCycle_sound p1229 1 10 true (1) (by decide) cert1229 m hm
#print axioms never1229


/-- Third-level first-hole refinement 1230, 1RB---_1RC1LE_0RD---_1LD1RB_0RB0RE_------; entry 1, period 10. -/
def p1230 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1230 : zipCycle p1230 1 10 true (1) = true := by decide +kernel
theorem never1230 (m : Machine) (hm : compatible p1230 m) : NeverHalts m :=
  zipCycle_sound p1230 1 10 true (1) (by decide) cert1230 m hm
#print axioms never1230


/-- Third-level first-hole refinement 1231, 1RB---_1RC1LE_0RD---_1LD1RB_1RB0RE_------; entry 1, period 10. -/
def p1231 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1231 : zipCycle p1231 1 10 true (1) = true := by decide +kernel
theorem never1231 (m : Machine) (hm : compatible p1231 m) : NeverHalts m :=
  zipCycle_sound p1231 1 10 true (1) (by decide) cert1231 m hm
#print axioms never1231


/-- Third-level first-hole refinement 1232, 1RB---_1RC1LE_0RD---_1LD1RB_0LC0RE_------; entry 25, period 1. -/
def p1232 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1232 : zipCycle p1232 25 1 false (5) = true := by decide +kernel
theorem never1232 (m : Machine) (hm : compatible p1232 m) : NeverHalts m :=
  zipCycle_sound p1232 25 1 false (5) (by decide) cert1232 m hm
#print axioms never1232


/-- Third-level first-hole refinement 1233, 1RB---_1RC1LE_0RD---_1LD1RB_1LC0RE_------; entry 1, period 12. -/
def p1233 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1233 : zipCycle p1233 1 12 true (1) = true := by decide +kernel
theorem never1233 (m : Machine) (hm : compatible p1233 m) : NeverHalts m :=
  zipCycle_sound p1233 1 12 true (1) (by decide) cert1233 m hm
#print axioms never1233


/-- Third-level first-hole refinement 1234, 1RB---_1RC1LE_0RD---_1LD1RB_0RC0RE_------; entry 29, period 1. -/
def p1234 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1234 : zipCycle p1234 29 1 false (9) = true := by decide +kernel
theorem never1234 (m : Machine) (hm : compatible p1234 m) : NeverHalts m :=
  zipCycle_sound p1234 29 1 false (9) (by decide) cert1234 m hm
#print axioms never1234


/-- Third-level first-hole refinement 1235, 1RB---_1RC1LE_0RD---_1LD1RB_1RC0RE_------; entry 2, period 9. -/
def p1235 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1235 : zipCycle p1235 2 9 true (1) = true := by decide +kernel
theorem never1235 (m : Machine) (hm : compatible p1235 m) : NeverHalts m :=
  zipCycle_sound p1235 2 9 true (1) (by decide) cert1235 m hm
#print axioms never1235


/-- Third-level first-hole refinement 1236, 1RB---_1RC1LE_0RD---_1LD1RB_0LD0RE_------; entry 21, period 1. -/
def p1236 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1236 : zipCycle p1236 21 1 false (3) = true := by decide +kernel
theorem never1236 (m : Machine) (hm : compatible p1236 m) : NeverHalts m :=
  zipCycle_sound p1236 21 1 false (3) (by decide) cert1236 m hm
#print axioms never1236


/-- Third-level first-hole refinement 1237, 1RB---_1RC1LE_0RD---_1LD1RB_1LD0RE_------; entry 22, period 1. -/
def p1237 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1237 : zipCycle p1237 22 1 false (4) = true := by decide +kernel
theorem never1237 (m : Machine) (hm : compatible p1237 m) : NeverHalts m :=
  zipCycle_sound p1237 22 1 false (4) (by decide) cert1237 m hm
#print axioms never1237


/-- Third-level first-hole refinement 1238, 1RB---_1RC1LE_0RD---_1LD1RB_0RD0RE_------; entry 25, period 1. -/
def p1238 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1238 : zipCycle p1238 25 1 false (7) = true := by decide +kernel
theorem never1238 (m : Machine) (hm : compatible p1238 m) : NeverHalts m :=
  zipCycle_sound p1238 25 1 false (7) (by decide) cert1238 m hm
#print axioms never1238


/-- Third-level first-hole refinement 1239, 1RB---_1RC1LE_0RD---_1LD1RB_1RD0RE_------; entry 8, period 6. -/
def p1239 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1239 : zipCycle p1239 8 6 true (2) = true := by decide +kernel
theorem never1239 (m : Machine) (hm : compatible p1239 m) : NeverHalts m :=
  zipCycle_sound p1239 8 6 true (2) (by decide) cert1239 m hm
#print axioms never1239


/-- Third-level first-hole refinement 1240, 1RB---_1RC1LE_0RD---_1LD1RB_0LE0RE_------; entry 15, period 1. -/
def p1240 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1240 : zipCycle p1240 15 1 false (1) = true := by decide +kernel
theorem never1240 (m : Machine) (hm : compatible p1240 m) : NeverHalts m :=
  zipCycle_sound p1240 15 1 false (1) (by decide) cert1240 m hm
#print axioms never1240


/-- Third-level first-hole refinement 1241, 1RB---_1RC1LE_0RD---_1LD1RB_1LE0RE_------; entry 19, period 1. -/
def p1241 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1241 : zipCycle p1241 19 1 false (5) = true := by decide +kernel
theorem never1241 (m : Machine) (hm : compatible p1241 m) : NeverHalts m :=
  zipCycle_sound p1241 19 1 false (5) (by decide) cert1241 m hm
#print axioms never1241


/-- Third-level first-hole refinement 1242, 1RB---_1RC1LE_0RD---_1LD1RB_0RE0RE_------; entry 10, period 1. -/
def p1242 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1242 : zipCycle p1242 10 1 true (4) = true := by decide +kernel
theorem never1242 (m : Machine) (hm : compatible p1242 m) : NeverHalts m :=
  zipCycle_sound p1242 10 1 true (4) (by decide) cert1242 m hm
#print axioms never1242


/-- Third-level first-hole refinement 1243, 1RB---_1RC1LE_0RD---_1LD1RB_1RE0RE_------; entry 10, period 1. -/
def p1243 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1243 : zipCycle p1243 10 1 true (4) = true := by decide +kernel
theorem never1243 (m : Machine) (hm : compatible p1243 m) : NeverHalts m :=
  zipCycle_sound p1243 10 1 true (4) (by decide) cert1243 m hm
#print axioms never1243


/-- Third-level first-hole refinement 1244, 1RB---_1RC1LE_0RD---_1LD1RB_0RA1RE_------; entry 0, period 11. -/
def p1244 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1244 : zipCycle p1244 0 11 true (0) = true := by decide +kernel
theorem never1244 (m : Machine) (hm : compatible p1244 m) : NeverHalts m :=
  zipCycle_sound p1244 0 11 true (0) (by decide) cert1244 m hm
#print axioms never1244


/-- Third-level first-hole refinement 1245, 1RB---_1RC1LE_0RD---_1LD1RB_1RA1RE_------; entry 0, period 11. -/
def p1245 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1245 : zipCycle p1245 0 11 true (0) = true := by decide +kernel
theorem never1245 (m : Machine) (hm : compatible p1245 m) : NeverHalts m :=
  zipCycle_sound p1245 0 11 true (0) (by decide) cert1245 m hm
#print axioms never1245


/-- Third-level first-hole refinement 1246, 1RB---_1RC1LE_0RD---_1LD1RB_0LB1RE_------; entry 8, period 4. -/
def p1246 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1246 : zipCycle p1246 8 4 true (2) = true := by decide +kernel
theorem never1246 (m : Machine) (hm : compatible p1246 m) : NeverHalts m :=
  zipCycle_sound p1246 8 4 true (2) (by decide) cert1246 m hm
#print axioms never1246


/-- Third-level first-hole refinement 1247, 1RB---_1RC1LE_0RD---_1LD1RB_1LB1RE_------; entry 6, period 5. -/
def p1247 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1247 : zipCycle p1247 6 5 true (1) = true := by decide +kernel
theorem never1247 (m : Machine) (hm : compatible p1247 m) : NeverHalts m :=
  zipCycle_sound p1247 6 5 true (1) (by decide) cert1247 m hm
#print axioms never1247


/-- Third-level first-hole refinement 1248, 1RB---_1RC1LE_0RD---_1LD1RB_0RB1RE_------; entry 1, period 10. -/
def p1248 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1248 : zipCycle p1248 1 10 true (1) = true := by decide +kernel
theorem never1248 (m : Machine) (hm : compatible p1248 m) : NeverHalts m :=
  zipCycle_sound p1248 1 10 true (1) (by decide) cert1248 m hm
#print axioms never1248


/-- Third-level first-hole refinement 1249, 1RB---_1RC1LE_0RD---_1LD1RB_1RB1RE_------; entry 1, period 10. -/
def p1249 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1249 : zipCycle p1249 1 10 true (1) = true := by decide +kernel
theorem never1249 (m : Machine) (hm : compatible p1249 m) : NeverHalts m :=
  zipCycle_sound p1249 1 10 true (1) (by decide) cert1249 m hm
#print axioms never1249


/-- Third-level first-hole refinement 1250, 1RB---_1RC1LE_0RD---_1LD1RB_0RC1RE_------; entry 7, period 11. -/
def p1250 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1250 : zipCycle p1250 7 11 true (1) = true := by decide +kernel
theorem never1250 (m : Machine) (hm : compatible p1250 m) : NeverHalts m :=
  zipCycle_sound p1250 7 11 true (1) (by decide) cert1250 m hm
#print axioms never1250


/-- Third-level first-hole refinement 1251, 1RB---_1RC1LE_0RD---_1LD1RB_1RC1RE_------; entry 2, period 9. -/
def p1251 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1251 : zipCycle p1251 2 9 true (1) = true := by decide +kernel
theorem never1251 (m : Machine) (hm : compatible p1251 m) : NeverHalts m :=
  zipCycle_sound p1251 2 9 true (1) (by decide) cert1251 m hm
#print axioms never1251


/-- Third-level first-hole refinement 1252, 1RB---_1RC1LE_0RD---_1LD1RB_0LD1RE_------; entry 1, period 11. -/
def p1252 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1252 : zipCycle p1252 1 11 true (1) = true := by decide +kernel
theorem never1252 (m : Machine) (hm : compatible p1252 m) : NeverHalts m :=
  zipCycle_sound p1252 1 11 true (1) (by decide) cert1252 m hm
#print axioms never1252


/-- Third-level first-hole refinement 1253, 1RB---_1RC1LE_0RD---_1LD1RB_1LD1RE_------; entry 8, period 5. -/
def p1253 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1253 : zipCycle p1253 8 5 true (2) = true := by decide +kernel
theorem never1253 (m : Machine) (hm : compatible p1253 m) : NeverHalts m :=
  zipCycle_sound p1253 8 5 true (2) (by decide) cert1253 m hm
#print axioms never1253


/-- Third-level first-hole refinement 1254, 1RB---_1RC1LE_0RD---_1LD1RB_0RD1RE_------; entry 3, period 8. -/
def p1254 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1254 : zipCycle p1254 3 8 true (1) = true := by decide +kernel
theorem never1254 (m : Machine) (hm : compatible p1254 m) : NeverHalts m :=
  zipCycle_sound p1254 3 8 true (1) (by decide) cert1254 m hm
#print axioms never1254


/-- Third-level first-hole refinement 1255, 1RB---_1RC1LE_0RD---_1LD1RB_1RD1RE_------; entry 8, period 6. -/
def p1255 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1255 : zipCycle p1255 8 6 true (2) = true := by decide +kernel
theorem never1255 (m : Machine) (hm : compatible p1255 m) : NeverHalts m :=
  zipCycle_sound p1255 8 6 true (2) (by decide) cert1255 m hm
#print axioms never1255


/-- Third-level first-hole refinement 1256, 1RB---_1RC1LE_0RD---_1LD1RB_0LE1RE_------; entry 9, period 2. -/
def p1256 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1256 : zipCycle p1256 9 2 true (3) = true := by decide +kernel
theorem never1256 (m : Machine) (hm : compatible p1256 m) : NeverHalts m :=
  zipCycle_sound p1256 9 2 true (3) (by decide) cert1256 m hm
#print axioms never1256


/-- Third-level first-hole refinement 1257, 1RB---_1RC1LE_0RD---_1LD1RB_1LE1RE_------; entry 8, period 3. -/
def p1257 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1257 : zipCycle p1257 8 3 true (2) = true := by decide +kernel
theorem never1257 (m : Machine) (hm : compatible p1257 m) : NeverHalts m :=
  zipCycle_sound p1257 8 3 true (2) (by decide) cert1257 m hm
#print axioms never1257


/-- Third-level first-hole refinement 1258, 1RB---_1RC1LE_0RD---_1LD1RB_0RE1RE_------; entry 10, period 1. -/
def p1258 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1258 : zipCycle p1258 10 1 true (4) = true := by decide +kernel
theorem never1258 (m : Machine) (hm : compatible p1258 m) : NeverHalts m :=
  zipCycle_sound p1258 10 1 true (4) (by decide) cert1258 m hm
#print axioms never1258


/-- Third-level first-hole refinement 1259, 1RB---_1RC1LE_0RD---_1LD1RB_1RE1RE_------; entry 10, period 1. -/
def p1259 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1259 : zipCycle p1259 10 1 true (4) = true := by decide +kernel
theorem never1259 (m : Machine) (hm : compatible p1259 m) : NeverHalts m :=
  zipCycle_sound p1259 10 1 true (4) (by decide) cert1259 m hm
#print axioms never1259


/-- Third-level first-hole refinement 1260, 1RB---_1RC1LE_0RD---_1LD1RB_---0LF_---1RA; entry 6, period 4. -/
def p1260 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1260 : zipCycle p1260 6 4 true (0) = true := by decide +kernel
theorem never1260 (m : Machine) (hm : compatible p1260 m) : NeverHalts m :=
  zipCycle_sound p1260 6 4 true (0) (by decide) cert1260 m hm
#print axioms never1260


/-- Third-level first-hole refinement 1261, 1RB---_1RC1LE_0RD---_1LD1RB_---0LF_---0LC; entry 10, period 1. -/
def p1261 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1261 : zipCycle p1261 10 1 false (0) = true := by decide +kernel
theorem never1261 (m : Machine) (hm : compatible p1261 m) : NeverHalts m :=
  zipCycle_sound p1261 10 1 false (0) (by decide) cert1261 m hm
#print axioms never1261


/-- Third-level first-hole refinement 1262, 1RB---_1RC1LE_0RD---_1LD1RB_---0LF_---0LD; entry 9, period 1. -/
def p1262 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1262 : zipCycle p1262 9 1 false (-1) = true := by decide +kernel
theorem never1262 (m : Machine) (hm : compatible p1262 m) : NeverHalts m :=
  zipCycle_sound p1262 9 1 false (-1) (by decide) cert1262 m hm
#print axioms never1262


/-- Third-level first-hole refinement 1263, 1RB---_1RC1LE_0RD---_1LD1RB_---0LF_---1LD; entry 9, period 1. -/
def p1263 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1263 : zipCycle p1263 9 1 false (-1) = true := by decide +kernel
theorem never1263 (m : Machine) (hm : compatible p1263 m) : NeverHalts m :=
  zipCycle_sound p1263 9 1 false (-1) (by decide) cert1263 m hm
#print axioms never1263


/-- Third-level first-hole refinement 1264, 1RB---_1RC1LE_0RD---_1LD1RB_---0LF_---0RD; entry 9, period 1. -/
def p1264 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1264 : zipCycle p1264 9 1 false (1) = true := by decide +kernel
theorem never1264 (m : Machine) (hm : compatible p1264 m) : NeverHalts m :=
  zipCycle_sound p1264 9 1 false (1) (by decide) cert1264 m hm
#print axioms never1264


/-- Third-level first-hole refinement 1265, 1RB---_1RC1LE_0RD---_1LD1RB_---1LF_---0LC; entry 10, period 1. -/
def p1265 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1265 : zipCycle p1265 10 1 false (0) = true := by decide +kernel
theorem never1265 (m : Machine) (hm : compatible p1265 m) : NeverHalts m :=
  zipCycle_sound p1265 10 1 false (0) (by decide) cert1265 m hm
#print axioms never1265


/-- Third-level first-hole refinement 1266, 1RB---_1RC1LE_0RD---_1LD1RB_---1LF_---0LD; entry 9, period 1. -/
def p1266 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1266 : zipCycle p1266 9 1 false (-1) = true := by decide +kernel
theorem never1266 (m : Machine) (hm : compatible p1266 m) : NeverHalts m :=
  zipCycle_sound p1266 9 1 false (-1) (by decide) cert1266 m hm
#print axioms never1266


/-- Third-level first-hole refinement 1267, 1RB---_1RC1LE_0RD---_1LD1RB_---1LF_---1LD; entry 9, period 1. -/
def p1267 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1267 : zipCycle p1267 9 1 false (-1) = true := by decide +kernel
theorem never1267 (m : Machine) (hm : compatible p1267 m) : NeverHalts m :=
  zipCycle_sound p1267 9 1 false (-1) (by decide) cert1267 m hm
#print axioms never1267


/-- Third-level first-hole refinement 1268, 1RB---_1RC1LE_0RD---_1LD1RB_---1LF_---1RD; entry 5, period 4. -/
def p1268 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1268 : zipCycle p1268 5 4 true (0) = true := by decide +kernel
theorem never1268 (m : Machine) (hm : compatible p1268 m) : NeverHalts m :=
  zipCycle_sound p1268 5 4 true (0) (by decide) cert1268 m hm
#print axioms never1268


/-- Third-level first-hole refinement 1269, 1RB---_1RC1LE_0RD---_1LD1RB_---1LF_---1RE; entry 7, period 2. -/
def p1269 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1269 : zipCycle p1269 7 2 true (0) = true := by decide +kernel
theorem never1269 (m : Machine) (hm : compatible p1269 m) : NeverHalts m :=
  zipCycle_sound p1269 7 2 true (0) (by decide) cert1269 m hm
#print axioms never1269


/-- Third-level first-hole refinement 1270, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---1LA; entry 6, period 4. -/
def p1270 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1270 : zipCycle p1270 6 4 true (1) = true := by decide +kernel
theorem never1270 (m : Machine) (hm : compatible p1270 m) : NeverHalts m :=
  zipCycle_sound p1270 6 4 true (1) (by decide) cert1270 m hm
#print axioms never1270


/-- Third-level first-hole refinement 1271, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---0LB; entry 1, period 11. -/
def p1271 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1271 : zipCycle p1271 1 11 true (1) = true := by decide +kernel
theorem never1271 (m : Machine) (hm : compatible p1271 m) : NeverHalts m :=
  zipCycle_sound p1271 1 11 true (1) (by decide) cert1271 m hm
#print axioms never1271


/-- Third-level first-hole refinement 1272, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---1RB; entry 1, period 11. -/
def p1272 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1272 : zipCycle p1272 1 11 true (1) = true := by decide +kernel
theorem never1272 (m : Machine) (hm : compatible p1272 m) : NeverHalts m :=
  zipCycle_sound p1272 1 11 true (1) (by decide) cert1272 m hm
#print axioms never1272


/-- Third-level first-hole refinement 1273, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---0LC; entry 17, period 1. -/
def p1273 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1273 : zipCycle p1273 17 1 false (1) = true := by decide +kernel
theorem never1273 (m : Machine) (hm : compatible p1273 m) : NeverHalts m :=
  zipCycle_sound p1273 17 1 false (1) (by decide) cert1273 m hm
#print axioms never1273


/-- Third-level first-hole refinement 1274, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---1LC; entry 1, period 15. -/
def p1274 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1274 : zipCycle p1274 1 15 true (1) = true := by decide +kernel
theorem never1274 (m : Machine) (hm : compatible p1274 m) : NeverHalts m :=
  zipCycle_sound p1274 1 15 true (1) (by decide) cert1274 m hm
#print axioms never1274


/-- Third-level first-hole refinement 1275, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---0LD; entry 14, period 1. -/
def p1275 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1275 : zipCycle p1275 14 1 false (0) = true := by decide +kernel
theorem never1275 (m : Machine) (hm : compatible p1275 m) : NeverHalts m :=
  zipCycle_sound p1275 14 1 false (0) (by decide) cert1275 m hm
#print axioms never1275


/-- Third-level first-hole refinement 1276, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---1LD; entry 14, period 1. -/
def p1276 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1276 : zipCycle p1276 14 1 false (0) = true := by decide +kernel
theorem never1276 (m : Machine) (hm : compatible p1276 m) : NeverHalts m :=
  zipCycle_sound p1276 14 1 false (0) (by decide) cert1276 m hm
#print axioms never1276


/-- Third-level first-hole refinement 1277, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---0RD; entry 1, period 9. -/
def p1277 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1277 : zipCycle p1277 1 9 true (1) = true := by decide +kernel
theorem never1277 (m : Machine) (hm : compatible p1277 m) : NeverHalts m :=
  zipCycle_sound p1277 1 9 true (1) (by decide) cert1277 m hm
#print axioms never1277


/-- Third-level first-hole refinement 1278, 1RB---_1RC1LE_0RD---_1LD1RB_---0RF_---1RD; entry 1, period 9. -/
def p1278 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1278 : zipCycle p1278 1 9 true (1) = true := by decide +kernel
theorem never1278 (m : Machine) (hm : compatible p1278 m) : NeverHalts m :=
  zipCycle_sound p1278 1 9 true (1) (by decide) cert1278 m hm
#print axioms never1278


/-- Third-level first-hole refinement 1279, 1RB---_1RC1LE_0RD---_1LD1RB_---1RF_---1RB; entry 1, period 11. -/
def p1279 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1279 : zipCycle p1279 1 11 true (1) = true := by decide +kernel
theorem never1279 (m : Machine) (hm : compatible p1279 m) : NeverHalts m :=
  zipCycle_sound p1279 1 11 true (1) (by decide) cert1279 m hm
#print axioms never1279


/-- Third-level first-hole refinement 1280, 1RB---_1RC1LE_0RD---_1LD1RB_---1RF_---1LD; entry 5, period 4. -/
def p1280 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1280 : zipCycle p1280 5 4 true (1) = true := by decide +kernel
theorem never1280 (m : Machine) (hm : compatible p1280 m) : NeverHalts m :=
  zipCycle_sound p1280 5 4 true (1) (by decide) cert1280 m hm
#print axioms never1280


/-- Third-level first-hole refinement 1281, 1RB---_1RC1LE_0RD---_1LD1RB_---1RF_---0RD; entry 1, period 9. -/
def p1281 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1281 : zipCycle p1281 1 9 true (1) = true := by decide +kernel
theorem never1281 (m : Machine) (hm : compatible p1281 m) : NeverHalts m :=
  zipCycle_sound p1281 1 9 true (1) (by decide) cert1281 m hm
#print axioms never1281


/-- Third-level first-hole refinement 1282, 1RB---_1RC1LE_0RD---_1LD1RB_---1RF_---1RD; entry 1, period 9. -/
def p1282 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1282 : zipCycle p1282 1 9 true (1) = true := by decide +kernel
theorem never1282 (m : Machine) (hm : compatible p1282 m) : NeverHalts m :=
  zipCycle_sound p1282 1 9 true (1) (by decide) cert1282 m hm
#print axioms never1282


/-- Third-level first-hole refinement 1283, 1RB---_1RC1LE_0RD---_1LD1RB_---1RF_---1LE; entry 7, period 2. -/
def p1283 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1283 : zipCycle p1283 7 2 true (1) = true := by decide +kernel
theorem never1283 (m : Machine) (hm : compatible p1283 m) : NeverHalts m :=
  zipCycle_sound p1283 7 2 true (1) (by decide) cert1283 m hm
#print axioms never1283


/-- Third-level first-hole refinement 1284, 1RB---_1RC0RE_0RD---_1LD1RB_0LA1LA_------; entry 0, period 11. -/
def p1284 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1284 : zipCycle p1284 0 11 true (0) = true := by decide +kernel
theorem never1284 (m : Machine) (hm : compatible p1284 m) : NeverHalts m :=
  zipCycle_sound p1284 0 11 true (0) (by decide) cert1284 m hm
#print axioms never1284


/-- Third-level first-hole refinement 1285, 1RB---_1RC0RE_0RD---_1LD1RB_1LA1LA_------; entry 8, period 3. -/
def p1285 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1285 : zipCycle p1285 8 3 true (2) = true := by decide +kernel
theorem never1285 (m : Machine) (hm : compatible p1285 m) : NeverHalts m :=
  zipCycle_sound p1285 8 3 true (2) (by decide) cert1285 m hm
#print axioms never1285


/-- Third-level first-hole refinement 1286, 1RB---_1RC0RE_0RD---_1LD1RB_0RA1LA_------; entry 0, period 11. -/
def p1286 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1286 : zipCycle p1286 0 11 true (0) = true := by decide +kernel
theorem never1286 (m : Machine) (hm : compatible p1286 m) : NeverHalts m :=
  zipCycle_sound p1286 0 11 true (0) (by decide) cert1286 m hm
#print axioms never1286


/-- Third-level first-hole refinement 1287, 1RB---_1RC0RE_0RD---_1LD1RB_1RA1LA_------; entry 0, period 11. -/
def p1287 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1287 : zipCycle p1287 0 11 true (0) = true := by decide +kernel
theorem never1287 (m : Machine) (hm : compatible p1287 m) : NeverHalts m :=
  zipCycle_sound p1287 0 11 true (0) (by decide) cert1287 m hm
#print axioms never1287


/-- Third-level first-hole refinement 1288, 1RB---_1RC0RE_0RD---_1LD1RB_0LB1LA_------; entry 1, period 10. -/
def p1288 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1288 : zipCycle p1288 1 10 true (1) = true := by decide +kernel
theorem never1288 (m : Machine) (hm : compatible p1288 m) : NeverHalts m :=
  zipCycle_sound p1288 1 10 true (1) (by decide) cert1288 m hm
#print axioms never1288


/-- Third-level first-hole refinement 1289, 1RB---_1RC0RE_0RD---_1LD1RB_0RB1LA_------; entry 1, period 10. -/
def p1289 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1289 : zipCycle p1289 1 10 true (1) = true := by decide +kernel
theorem never1289 (m : Machine) (hm : compatible p1289 m) : NeverHalts m :=
  zipCycle_sound p1289 1 10 true (1) (by decide) cert1289 m hm
#print axioms never1289


/-- Third-level first-hole refinement 1290, 1RB---_1RC0RE_0RD---_1LD1RB_1RB1LA_------; entry 1, period 10. -/
def p1290 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1290 : zipCycle p1290 1 10 true (1) = true := by decide +kernel
theorem never1290 (m : Machine) (hm : compatible p1290 m) : NeverHalts m :=
  zipCycle_sound p1290 1 10 true (1) (by decide) cert1290 m hm
#print axioms never1290


/-- Third-level first-hole refinement 1291, 1RB---_1RC0RE_0RD---_1LD1RB_0LC1LA_------; entry 2, period 9. -/
def p1291 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1291 : zipCycle p1291 2 9 true (1) = true := by decide +kernel
theorem never1291 (m : Machine) (hm : compatible p1291 m) : NeverHalts m :=
  zipCycle_sound p1291 2 9 true (1) (by decide) cert1291 m hm
#print axioms never1291


/-- Third-level first-hole refinement 1292, 1RB---_1RC0RE_0RD---_1LD1RB_1LC1LA_------; entry 1, period 12. -/
def p1292 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1292 : zipCycle p1292 1 12 true (1) = true := by decide +kernel
theorem never1292 (m : Machine) (hm : compatible p1292 m) : NeverHalts m :=
  zipCycle_sound p1292 1 12 true (1) (by decide) cert1292 m hm
#print axioms never1292


/-- Third-level first-hole refinement 1293, 1RB---_1RC0RE_0RD---_1LD1RB_0RC1LA_------; entry 6, period 17. -/
def p1293 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1293 : zipCycle p1293 6 17 true (2) = true := by decide +kernel
theorem never1293 (m : Machine) (hm : compatible p1293 m) : NeverHalts m :=
  zipCycle_sound p1293 6 17 true (2) (by decide) cert1293 m hm
#print axioms never1293


/-- Third-level first-hole refinement 1294, 1RB---_1RC0RE_0RD---_1LD1RB_1RC1LA_------; entry 2, period 9. -/
def p1294 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1294 : zipCycle p1294 2 9 true (1) = true := by decide +kernel
theorem never1294 (m : Machine) (hm : compatible p1294 m) : NeverHalts m :=
  zipCycle_sound p1294 2 9 true (1) (by decide) cert1294 m hm
#print axioms never1294


/-- Third-level first-hole refinement 1295, 1RB---_1RC0RE_0RD---_1LD1RB_0LD1LA_------; entry 9, period 4. -/
def p1295 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1295 : zipCycle p1295 9 4 true (2) = true := by decide +kernel
theorem never1295 (m : Machine) (hm : compatible p1295 m) : NeverHalts m :=
  zipCycle_sound p1295 9 4 true (2) (by decide) cert1295 m hm
#print axioms never1295


/-- Third-level first-hole refinement 1296, 1RB---_1RC0RE_0RD---_1LD1RB_1LD1LA_------; entry 4, period 7. -/
def p1296 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1296 : zipCycle p1296 4 7 true (1) = true := by decide +kernel
theorem never1296 (m : Machine) (hm : compatible p1296 m) : NeverHalts m :=
  zipCycle_sound p1296 4 7 true (1) (by decide) cert1296 m hm
#print axioms never1296


/-- Third-level first-hole refinement 1297, 1RB---_1RC0RE_0RD---_1LD1RB_0RD1LA_------; entry 6, period 12. -/
def p1297 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1297 : zipCycle p1297 6 12 true (2) = true := by decide +kernel
theorem never1297 (m : Machine) (hm : compatible p1297 m) : NeverHalts m :=
  zipCycle_sound p1297 6 12 true (2) (by decide) cert1297 m hm
#print axioms never1297


/-- Third-level first-hole refinement 1298, 1RB---_1RC0RE_0RD---_1LD1RB_1RD1LA_------; entry 9, period 4. -/
def p1298 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1298 : zipCycle p1298 9 4 true (3) = true := by decide +kernel
theorem never1298 (m : Machine) (hm : compatible p1298 m) : NeverHalts m :=
  zipCycle_sound p1298 9 4 true (3) (by decide) cert1298 m hm
#print axioms never1298


/-- Third-level first-hole refinement 1299, 1RB---_1RC0RE_0RD---_1LD1RB_0RE1LA_------; entry 10, period 1. -/
def p1299 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1299 : zipCycle p1299 10 1 true (4) = true := by decide +kernel
theorem never1299 (m : Machine) (hm : compatible p1299 m) : NeverHalts m :=
  zipCycle_sound p1299 10 1 true (4) (by decide) cert1299 m hm
#print axioms never1299

end BB6.Agent24Raw45D3_12
