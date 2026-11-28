import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_11
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1100, 1RB1RE_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 0, period 10. -/
def p1100 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1100 : zipCycle p1100 0 10 true (0) = true := by decide +kernel
theorem never1100 (m : Machine) (hm : compatible p1100 m) : NeverHalts m :=
  zipCycle_sound p1100 0 10 true (0) (by decide) cert1100 m hm
#print axioms never1100


/-- Third-level first-hole refinement 1101, 1RB0LA_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 0, period 11. -/
def p1101 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1101 : zipCycle p1101 0 11 false (3) = true := by decide +kernel
theorem never1101 (m : Machine) (hm : compatible p1101 m) : NeverHalts m :=
  zipCycle_sound p1101 0 11 false (3) (by decide) cert1101 m hm
#print axioms never1101


/-- Third-level first-hole refinement 1102, 1RB1LA_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 9, period 5. -/
def p1102 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1102 : zipCycle p1102 9 5 false (1) = true := by decide +kernel
theorem never1102 (m : Machine) (hm : compatible p1102 m) : NeverHalts m :=
  zipCycle_sound p1102 9 5 false (1) (by decide) cert1102 m hm
#print axioms never1102


/-- Third-level first-hole refinement 1103, 1RB0RA_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 0, period 10. -/
def p1103 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1103 : zipCycle p1103 0 10 true (0) = true := by decide +kernel
theorem never1103 (m : Machine) (hm : compatible p1103 m) : NeverHalts m :=
  zipCycle_sound p1103 0 10 true (0) (by decide) cert1103 m hm
#print axioms never1103


/-- Third-level first-hole refinement 1104, 1RB1RA_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 0, period 10. -/
def p1104 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1104 : zipCycle p1104 0 10 true (0) = true := by decide +kernel
theorem never1104 (m : Machine) (hm : compatible p1104 m) : NeverHalts m :=
  zipCycle_sound p1104 0 10 true (0) (by decide) cert1104 m hm
#print axioms never1104


/-- Third-level first-hole refinement 1105, 1RB1RB_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 1, period 11. -/
def p1105 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1105 : zipCycle p1105 1 11 true (1) = true := by decide +kernel
theorem never1105 (m : Machine) (hm : compatible p1105 m) : NeverHalts m :=
  zipCycle_sound p1105 1 11 true (1) (by decide) cert1105 m hm
#print axioms never1105


/-- Third-level first-hole refinement 1106, 1RB1LD_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 5, period 4. -/
def p1106 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1106 : zipCycle p1106 5 4 true (1) = true := by decide +kernel
theorem never1106 (m : Machine) (hm : compatible p1106 m) : NeverHalts m :=
  zipCycle_sound p1106 5 4 true (1) (by decide) cert1106 m hm
#print axioms never1106


/-- Third-level first-hole refinement 1107, 1RB0RD_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 1, period 9. -/
def p1107 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1107 : zipCycle p1107 1 9 true (1) = true := by decide +kernel
theorem never1107 (m : Machine) (hm : compatible p1107 m) : NeverHalts m :=
  zipCycle_sound p1107 1 9 true (1) (by decide) cert1107 m hm
#print axioms never1107


/-- Third-level first-hole refinement 1108, 1RB1RD_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 1, period 9. -/
def p1108 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1108 : zipCycle p1108 1 9 true (1) = true := by decide +kernel
theorem never1108 (m : Machine) (hm : compatible p1108 m) : NeverHalts m :=
  zipCycle_sound p1108 1 9 true (1) (by decide) cert1108 m hm
#print axioms never1108


/-- Third-level first-hole refinement 1109, 1RB0LE_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 0, period 15. -/
def p1109 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1109 : zipCycle p1109 0 15 true (0) = true := by decide +kernel
theorem never1109 (m : Machine) (hm : compatible p1109 m) : NeverHalts m :=
  zipCycle_sound p1109 0 15 true (0) (by decide) cert1109 m hm
#print axioms never1109


/-- Third-level first-hole refinement 1110, 1RB1LE_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 7, period 2. -/
def p1110 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1110 : zipCycle p1110 7 2 true (1) = true := by decide +kernel
theorem never1110 (m : Machine) (hm : compatible p1110 m) : NeverHalts m :=
  zipCycle_sound p1110 7 2 true (1) (by decide) cert1110 m hm
#print axioms never1110


/-- Third-level first-hole refinement 1111, 1RB0RE_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 0, period 10. -/
def p1111 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1111 : zipCycle p1111 0 10 true (0) = true := by decide +kernel
theorem never1111 (m : Machine) (hm : compatible p1111 m) : NeverHalts m :=
  zipCycle_sound p1111 0 10 true (0) (by decide) cert1111 m hm
#print axioms never1111


/-- Third-level first-hole refinement 1112, 1RB1RE_1RC1LE_0RD---_1LD1RB_---1RA_------; entry 0, period 10. -/
def p1112 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1112 : zipCycle p1112 0 10 true (0) = true := by decide +kernel
theorem never1112 (m : Machine) (hm : compatible p1112 m) : NeverHalts m :=
  zipCycle_sound p1112 0 10 true (0) (by decide) cert1112 m hm
#print axioms never1112


/-- Third-level first-hole refinement 1113, 1RB---_1RC1LE_0RD---_1LD1RB_0RB0LB_------; entry 8, period 2. -/
def p1113 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1113 : zipCycle p1113 8 2 true (-1) = true := by decide +kernel
theorem never1113 (m : Machine) (hm : compatible p1113 m) : NeverHalts m :=
  zipCycle_sound p1113 8 2 true (-1) (by decide) cert1113 m hm
#print axioms never1113


/-- Third-level first-hole refinement 1114, 1RB---_1RC1LE_0RD---_1LD1RB_0LC0LB_------; entry 11, period 1. -/
def p1114 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1114 : zipCycle p1114 11 1 false (-1) = true := by decide +kernel
theorem never1114 (m : Machine) (hm : compatible p1114 m) : NeverHalts m :=
  zipCycle_sound p1114 11 1 false (-1) (by decide) cert1114 m hm
#print axioms never1114


/-- Third-level first-hole refinement 1115, 1RB---_1RC1LE_0RD---_1LD1RB_0LD0LB_------; entry 10, period 1. -/
def p1115 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1115 : zipCycle p1115 10 1 false (-2) = true := by decide +kernel
theorem never1115 (m : Machine) (hm : compatible p1115 m) : NeverHalts m :=
  zipCycle_sound p1115 10 1 false (-2) (by decide) cert1115 m hm
#print axioms never1115


/-- Third-level first-hole refinement 1116, 1RB---_1RC1LE_0RD---_1LD1RB_1LD0LB_------; entry 10, period 1. -/
def p1116 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1116 : zipCycle p1116 10 1 false (-2) = true := by decide +kernel
theorem never1116 (m : Machine) (hm : compatible p1116 m) : NeverHalts m :=
  zipCycle_sound p1116 10 1 false (-2) (by decide) cert1116 m hm
#print axioms never1116


/-- Third-level first-hole refinement 1117, 1RB---_1RC1LE_0RD---_1LD1RB_0LE0LB_------; entry 9, period 1. -/
def p1117 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1117 : zipCycle p1117 9 1 false (-1) = true := by decide +kernel
theorem never1117 (m : Machine) (hm : compatible p1117 m) : NeverHalts m :=
  zipCycle_sound p1117 9 1 false (-1) (by decide) cert1117 m hm
#print axioms never1117


/-- Third-level first-hole refinement 1118, 1RB---_1RC1LE_0RD---_1LD1RB_1LE0LB_------; entry 9, period 1. -/
def p1118 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1118 : zipCycle p1118 9 1 false (-1) = true := by decide +kernel
theorem never1118 (m : Machine) (hm : compatible p1118 m) : NeverHalts m :=
  zipCycle_sound p1118 9 1 false (-1) (by decide) cert1118 m hm
#print axioms never1118


/-- Third-level first-hole refinement 1119, 1RB---_1RC1LE_0RD---_1LD1RB_1RE0LB_------; entry 7, period 3. -/
def p1119 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1119 : zipCycle p1119 7 3 false (1) = true := by decide +kernel
theorem never1119 (m : Machine) (hm : compatible p1119 m) : NeverHalts m :=
  zipCycle_sound p1119 7 3 false (1) (by decide) cert1119 m hm
#print axioms never1119


/-- Third-level first-hole refinement 1120, 1RB---_1RC1LE_0RD---_1LD1RB_0RB1LB_------; entry 8, period 2. -/
def p1120 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1120 : zipCycle p1120 8 2 true (-1) = true := by decide +kernel
theorem never1120 (m : Machine) (hm : compatible p1120 m) : NeverHalts m :=
  zipCycle_sound p1120 8 2 true (-1) (by decide) cert1120 m hm
#print axioms never1120


/-- Third-level first-hole refinement 1121, 1RB---_1RC1LE_0RD---_1LD1RB_0LC1LB_------; entry 11, period 1. -/
def p1121 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1121 : zipCycle p1121 11 1 false (-1) = true := by decide +kernel
theorem never1121 (m : Machine) (hm : compatible p1121 m) : NeverHalts m :=
  zipCycle_sound p1121 11 1 false (-1) (by decide) cert1121 m hm
#print axioms never1121


/-- Third-level first-hole refinement 1122, 1RB---_1RC1LE_0RD---_1LD1RB_0LD1LB_------; entry 10, period 1. -/
def p1122 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1122 : zipCycle p1122 10 1 false (-2) = true := by decide +kernel
theorem never1122 (m : Machine) (hm : compatible p1122 m) : NeverHalts m :=
  zipCycle_sound p1122 10 1 false (-2) (by decide) cert1122 m hm
#print axioms never1122


/-- Third-level first-hole refinement 1123, 1RB---_1RC1LE_0RD---_1LD1RB_1LD1LB_------; entry 10, period 1. -/
def p1123 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1123 : zipCycle p1123 10 1 false (-2) = true := by decide +kernel
theorem never1123 (m : Machine) (hm : compatible p1123 m) : NeverHalts m :=
  zipCycle_sound p1123 10 1 false (-2) (by decide) cert1123 m hm
#print axioms never1123


/-- Third-level first-hole refinement 1124, 1RB---_1RC1LE_0RD---_1LD1RB_1RD1LB_------; entry 5, period 5. -/
def p1124 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1124 : zipCycle p1124 5 5 false (2) = true := by decide +kernel
theorem never1124 (m : Machine) (hm : compatible p1124 m) : NeverHalts m :=
  zipCycle_sound p1124 5 5 false (2) (by decide) cert1124 m hm
#print axioms never1124


/-- Third-level first-hole refinement 1125, 1RB---_1RC1LE_0RD---_1LD1RB_0LE1LB_------; entry 9, period 1. -/
def p1125 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1125 : zipCycle p1125 9 1 false (-1) = true := by decide +kernel
theorem never1125 (m : Machine) (hm : compatible p1125 m) : NeverHalts m :=
  zipCycle_sound p1125 9 1 false (-1) (by decide) cert1125 m hm
#print axioms never1125


/-- Third-level first-hole refinement 1126, 1RB---_1RC1LE_0RD---_1LD1RB_1LE1LB_------; entry 9, period 1. -/
def p1126 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1126 : zipCycle p1126 9 1 false (-1) = true := by decide +kernel
theorem never1126 (m : Machine) (hm : compatible p1126 m) : NeverHalts m :=
  zipCycle_sound p1126 9 1 false (-1) (by decide) cert1126 m hm
#print axioms never1126


/-- Third-level first-hole refinement 1127, 1RB---_1RC1LE_0RD---_1LD1RB_1RE1LB_------; entry 7, period 3. -/
def p1127 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1127 : zipCycle p1127 7 3 false (1) = true := by decide +kernel
theorem never1127 (m : Machine) (hm : compatible p1127 m) : NeverHalts m :=
  zipCycle_sound p1127 7 3 false (1) (by decide) cert1127 m hm
#print axioms never1127


/-- Third-level first-hole refinement 1128, 1RB---_1RC1LE_0RD---_1LD1RB_0RB0RB_------; entry 8, period 2. -/
def p1128 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1128 : zipCycle p1128 8 2 true (1) = true := by decide +kernel
theorem never1128 (m : Machine) (hm : compatible p1128 m) : NeverHalts m :=
  zipCycle_sound p1128 8 2 true (1) (by decide) cert1128 m hm
#print axioms never1128


/-- Third-level first-hole refinement 1129, 1RB---_1RC1LE_0RD---_1LD1RB_1RB0RB_------; entry 6, period 4. -/
def p1129 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1129 : zipCycle p1129 6 4 true (1) = true := by decide +kernel
theorem never1129 (m : Machine) (hm : compatible p1129 m) : NeverHalts m :=
  zipCycle_sound p1129 6 4 true (1) (by decide) cert1129 m hm
#print axioms never1129


/-- Third-level first-hole refinement 1130, 1RB---_1RC1LE_0RD---_1LD1RB_1LD0RB_------; entry 15, period 1. -/
def p1130 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1130 : zipCycle p1130 15 1 false (-1) = true := by decide +kernel
theorem never1130 (m : Machine) (hm : compatible p1130 m) : NeverHalts m :=
  zipCycle_sound p1130 15 1 false (-1) (by decide) cert1130 m hm
#print axioms never1130


/-- Third-level first-hole refinement 1131, 1RB---_1RC1LE_0RD---_1LD1RB_0RD0RB_------; entry 1, period 15. -/
def p1131 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1131 : zipCycle p1131 1 15 true (1) = true := by decide +kernel
theorem never1131 (m : Machine) (hm : compatible p1131 m) : NeverHalts m :=
  zipCycle_sound p1131 1 15 true (1) (by decide) cert1131 m hm
#print axioms never1131


/-- Third-level first-hole refinement 1132, 1RB---_1RC1LE_0RD---_1LD1RB_1RD0RB_------; entry 1, period 15. -/
def p1132 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1132 : zipCycle p1132 1 15 true (1) = true := by decide +kernel
theorem never1132 (m : Machine) (hm : compatible p1132 m) : NeverHalts m :=
  zipCycle_sound p1132 1 15 true (1) (by decide) cert1132 m hm
#print axioms never1132


/-- Third-level first-hole refinement 1133, 1RB---_1RC1LE_0RD---_1LD1RB_1LE0RB_------; entry 12, period 1. -/
def p1133 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1133 : zipCycle p1133 12 1 false (0) = true := by decide +kernel
theorem never1133 (m : Machine) (hm : compatible p1133 m) : NeverHalts m :=
  zipCycle_sound p1133 12 1 false (0) (by decide) cert1133 m hm
#print axioms never1133


/-- Third-level first-hole refinement 1134, 1RB---_1RC1LE_0RD---_1LD1RB_0RE0RB_------; entry 1, period 13. -/
def p1134 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1134 : zipCycle p1134 1 13 true (1) = true := by decide +kernel
theorem never1134 (m : Machine) (hm : compatible p1134 m) : NeverHalts m :=
  zipCycle_sound p1134 1 13 true (1) (by decide) cert1134 m hm
#print axioms never1134


/-- Third-level first-hole refinement 1135, 1RB---_1RC1LE_0RD---_1LD1RB_1RE0RB_------; entry 1, period 13. -/
def p1135 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1135 : zipCycle p1135 1 13 true (1) = true := by decide +kernel
theorem never1135 (m : Machine) (hm : compatible p1135 m) : NeverHalts m :=
  zipCycle_sound p1135 1 13 true (1) (by decide) cert1135 m hm
#print axioms never1135


/-- Third-level first-hole refinement 1136, 1RB---_1RC1LE_0RD0LA_1LD1RB_---0LC_------; entry 2, period 13. -/
def p1136 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1136 : zipCycle p1136 2 13 false (3) = true := by decide +kernel
theorem never1136 (m : Machine) (hm : compatible p1136 m) : NeverHalts m :=
  zipCycle_sound p1136 2 13 false (3) (by decide) cert1136 m hm
#print axioms never1136


/-- Third-level first-hole refinement 1137, 1RB---_1RC1LE_0RD1LA_1LD1RB_---0LC_------; entry 13, period 1. -/
def p1137 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1137 : zipCycle p1137 13 1 false (-1) = true := by decide +kernel
theorem never1137 (m : Machine) (hm : compatible p1137 m) : NeverHalts m :=
  zipCycle_sound p1137 13 1 false (-1) (by decide) cert1137 m hm
#print axioms never1137


/-- Third-level first-hole refinement 1138, 1RB---_1RC1LE_0RD0RA_1LD1RB_---0LC_------; entry 13, period 1. -/
def p1138 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1138 : zipCycle p1138 13 1 false (1) = true := by decide +kernel
theorem never1138 (m : Machine) (hm : compatible p1138 m) : NeverHalts m :=
  zipCycle_sound p1138 13 1 false (1) (by decide) cert1138 m hm
#print axioms never1138


/-- Third-level first-hole refinement 1139, 1RB---_1RC1LE_0RD1RA_1LD1RB_---0LC_------; entry 6, period 4. -/
def p1139 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1139 : zipCycle p1139 6 4 true (0) = true := by decide +kernel
theorem never1139 (m : Machine) (hm : compatible p1139 m) : NeverHalts m :=
  zipCycle_sound p1139 6 4 true (0) (by decide) cert1139 m hm
#print axioms never1139


/-- Third-level first-hole refinement 1140, 1RB---_1RC1LE_0RD0LB_1LD1RB_---0LC_------; entry 17, period 1. -/
def p1140 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1140 : zipCycle p1140 17 1 false (-1) = true := by decide +kernel
theorem never1140 (m : Machine) (hm : compatible p1140 m) : NeverHalts m :=
  zipCycle_sound p1140 17 1 false (-1) (by decide) cert1140 m hm
#print axioms never1140


/-- Third-level first-hole refinement 1141, 1RB---_1RC1LE_0RD1RB_1LD1RB_---0LC_------; entry 1, period 15. -/
def p1141 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1141 : zipCycle p1141 1 15 true (0) = true := by decide +kernel
theorem never1141 (m : Machine) (hm : compatible p1141 m) : NeverHalts m :=
  zipCycle_sound p1141 1 15 true (0) (by decide) cert1141 m hm
#print axioms never1141


/-- Third-level first-hole refinement 1142, 1RB---_1RC1LE_0RD0LC_1LD1RB_---0LC_------; entry 10, period 1. -/
def p1142 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1142 : zipCycle p1142 10 1 false (0) = true := by decide +kernel
theorem never1142 (m : Machine) (hm : compatible p1142 m) : NeverHalts m :=
  zipCycle_sound p1142 10 1 false (0) (by decide) cert1142 m hm
#print axioms never1142


/-- Third-level first-hole refinement 1143, 1RB---_1RC1LE_0RD1LC_1LD1RB_---0LC_------; entry 20, period 1. -/
def p1143 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1143 : zipCycle p1143 20 1 false (0) = true := by decide +kernel
theorem never1143 (m : Machine) (hm : compatible p1143 m) : NeverHalts m :=
  zipCycle_sound p1143 20 1 false (0) (by decide) cert1143 m hm
#print axioms never1143


/-- Third-level first-hole refinement 1144, 1RB---_1RC1LE_0RD0RC_1LD1RB_---0LC_------; entry 14, period 1. -/
def p1144 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1144 : zipCycle p1144 14 1 false (2) = true := by decide +kernel
theorem never1144 (m : Machine) (hm : compatible p1144 m) : NeverHalts m :=
  zipCycle_sound p1144 14 1 false (2) (by decide) cert1144 m hm
#print axioms never1144


/-- Third-level first-hole refinement 1145, 1RB---_1RC1LE_0RD1RC_1LD1RB_---0LC_------; entry 20, period 1. -/
def p1145 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1145 : zipCycle p1145 20 1 false (0) = true := by decide +kernel
theorem never1145 (m : Machine) (hm : compatible p1145 m) : NeverHalts m :=
  zipCycle_sound p1145 20 1 false (0) (by decide) cert1145 m hm
#print axioms never1145


/-- Third-level first-hole refinement 1146, 1RB---_1RC1LE_0RD0LD_1LD1RB_---0LC_------; entry 9, period 1. -/
def p1146 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1146 : zipCycle p1146 9 1 false (-1) = true := by decide +kernel
theorem never1146 (m : Machine) (hm : compatible p1146 m) : NeverHalts m :=
  zipCycle_sound p1146 9 1 false (-1) (by decide) cert1146 m hm
#print axioms never1146


/-- Third-level first-hole refinement 1147, 1RB---_1RC1LE_0RD1LD_1LD1RB_---0LC_------; entry 9, period 1. -/
def p1147 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1147 : zipCycle p1147 9 1 false (-1) = true := by decide +kernel
theorem never1147 (m : Machine) (hm : compatible p1147 m) : NeverHalts m :=
  zipCycle_sound p1147 9 1 false (-1) (by decide) cert1147 m hm
#print axioms never1147


/-- Third-level first-hole refinement 1148, 1RB---_1RC1LE_0RD0RD_1LD1RB_---0LC_------; entry 9, period 1. -/
def p1148 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1148 : zipCycle p1148 9 1 false (1) = true := by decide +kernel
theorem never1148 (m : Machine) (hm : compatible p1148 m) : NeverHalts m :=
  zipCycle_sound p1148 9 1 false (1) (by decide) cert1148 m hm
#print axioms never1148


/-- Third-level first-hole refinement 1149, 1RB---_1RC1LE_0RD1RD_1LD1RB_---0LC_------; entry 14, period 1. -/
def p1149 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1149 : zipCycle p1149 14 1 false (0) = true := by decide +kernel
theorem never1149 (m : Machine) (hm : compatible p1149 m) : NeverHalts m :=
  zipCycle_sound p1149 14 1 false (0) (by decide) cert1149 m hm
#print axioms never1149


/-- Third-level first-hole refinement 1150, 1RB---_1RC1LE_0RD1LA_1LD1RB_---1LC_------; entry 10, period 4. -/
def p1150 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1150 : zipCycle p1150 10 4 true (-2) = true := by decide +kernel
theorem never1150 (m : Machine) (hm : compatible p1150 m) : NeverHalts m :=
  zipCycle_sound p1150 10 4 true (-2) (by decide) cert1150 m hm
#print axioms never1150


/-- Third-level first-hole refinement 1151, 1RB---_1RC1LE_0RD0LB_1LD1RB_---1LC_------; entry 10, period 4. -/
def p1151 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1151 : zipCycle p1151 10 4 true (0) = true := by decide +kernel
theorem never1151 (m : Machine) (hm : compatible p1151 m) : NeverHalts m :=
  zipCycle_sound p1151 10 4 true (0) (by decide) cert1151 m hm
#print axioms never1151


/-- Third-level first-hole refinement 1152, 1RB---_1RC1LE_0RD1RB_1LD1RB_---1LC_------; entry 9, period 4. -/
def p1152 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1152 : zipCycle p1152 9 4 true (-1) = true := by decide +kernel
theorem never1152 (m : Machine) (hm : compatible p1152 m) : NeverHalts m :=
  zipCycle_sound p1152 9 4 true (-1) (by decide) cert1152 m hm
#print axioms never1152


/-- Third-level first-hole refinement 1153, 1RB---_1RC1LE_0RD0LC_1LD1RB_---1LC_------; entry 10, period 1. -/
def p1153 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1153 : zipCycle p1153 10 1 false (0) = true := by decide +kernel
theorem never1153 (m : Machine) (hm : compatible p1153 m) : NeverHalts m :=
  zipCycle_sound p1153 10 1 false (0) (by decide) cert1153 m hm
#print axioms never1153


/-- Third-level first-hole refinement 1154, 1RB---_1RC1LE_0RD1LC_1LD1RB_---1LC_------; entry 9, period 4. -/
def p1154 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1154 : zipCycle p1154 9 4 true (-1) = true := by decide +kernel
theorem never1154 (m : Machine) (hm : compatible p1154 m) : NeverHalts m :=
  zipCycle_sound p1154 9 4 true (-1) (by decide) cert1154 m hm
#print axioms never1154


/-- Third-level first-hole refinement 1155, 1RB---_1RC1LE_0RD0RC_1LD1RB_---1LC_------; entry 13, period 1. -/
def p1155 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1155 : zipCycle p1155 13 1 false (5) = true := by decide +kernel
theorem never1155 (m : Machine) (hm : compatible p1155 m) : NeverHalts m :=
  zipCycle_sound p1155 13 1 false (5) (by decide) cert1155 m hm
#print axioms never1155


/-- Third-level first-hole refinement 1156, 1RB---_1RC1LE_0RD1RC_1LD1RB_---1LC_------; entry 2, period 10. -/
def p1156 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1156 : zipCycle p1156 2 10 true (0) = true := by decide +kernel
theorem never1156 (m : Machine) (hm : compatible p1156 m) : NeverHalts m :=
  zipCycle_sound p1156 2 10 true (0) (by decide) cert1156 m hm
#print axioms never1156


/-- Third-level first-hole refinement 1157, 1RB---_1RC1LE_0RD0LD_1LD1RB_---1LC_------; entry 9, period 1. -/
def p1157 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1157 : zipCycle p1157 9 1 false (-1) = true := by decide +kernel
theorem never1157 (m : Machine) (hm : compatible p1157 m) : NeverHalts m :=
  zipCycle_sound p1157 9 1 false (-1) (by decide) cert1157 m hm
#print axioms never1157


/-- Third-level first-hole refinement 1158, 1RB---_1RC1LE_0RD1LD_1LD1RB_---1LC_------; entry 9, period 1. -/
def p1158 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1158 : zipCycle p1158 9 1 false (-1) = true := by decide +kernel
theorem never1158 (m : Machine) (hm : compatible p1158 m) : NeverHalts m :=
  zipCycle_sound p1158 9 1 false (-1) (by decide) cert1158 m hm
#print axioms never1158


/-- Third-level first-hole refinement 1159, 1RB---_1RC1LE_0RD0RD_1LD1RB_---1LC_------; entry 9, period 4. -/
def p1159 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1159 : zipCycle p1159 9 4 true (0) = true := by decide +kernel
theorem never1159 (m : Machine) (hm : compatible p1159 m) : NeverHalts m :=
  zipCycle_sound p1159 9 4 true (0) (by decide) cert1159 m hm
#print axioms never1159


/-- Third-level first-hole refinement 1160, 1RB---_1RC1LE_0RD1RD_1LD1RB_---1LC_------; entry 5, period 4. -/
def p1160 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1160 : zipCycle p1160 5 4 true (0) = true := by decide +kernel
theorem never1160 (m : Machine) (hm : compatible p1160 m) : NeverHalts m :=
  zipCycle_sound p1160 5 4 true (0) (by decide) cert1160 m hm
#print axioms never1160


/-- Third-level first-hole refinement 1161, 1RB---_1RC1LE_0RD0RE_1LD1RB_---1LC_------; entry 9, period 4. -/
def p1161 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1161 : zipCycle p1161 9 4 true (0) = true := by decide +kernel
theorem never1161 (m : Machine) (hm : compatible p1161 m) : NeverHalts m :=
  zipCycle_sound p1161 9 4 true (0) (by decide) cert1161 m hm
#print axioms never1161


/-- Third-level first-hole refinement 1162, 1RB---_1RC1LE_0RD1RE_1LD1RB_---1LC_------; entry 7, period 2. -/
def p1162 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1162 : zipCycle p1162 7 2 true (0) = true := by decide +kernel
theorem never1162 (m : Machine) (hm : compatible p1162 m) : NeverHalts m :=
  zipCycle_sound p1162 7 2 true (0) (by decide) cert1162 m hm
#print axioms never1162


/-- Third-level first-hole refinement 1163, 1RB---_1RC1LE_0RD1LA_1LD1RB_---0RC_------; entry 6, period 4. -/
def p1163 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1163 : zipCycle p1163 6 4 true (1) = true := by decide +kernel
theorem never1163 (m : Machine) (hm : compatible p1163 m) : NeverHalts m :=
  zipCycle_sound p1163 6 4 true (1) (by decide) cert1163 m hm
#print axioms never1163


/-- Third-level first-hole refinement 1164, 1RB---_1RC1LE_0RD0LB_1LD1RB_---0RC_------; entry 1, period 11. -/
def p1164 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1164 : zipCycle p1164 1 11 true (1) = true := by decide +kernel
theorem never1164 (m : Machine) (hm : compatible p1164 m) : NeverHalts m :=
  zipCycle_sound p1164 1 11 true (1) (by decide) cert1164 m hm
#print axioms never1164


/-- Third-level first-hole refinement 1165, 1RB---_1RC1LE_0RD1RB_1LD1RB_---0RC_------; entry 1, period 11. -/
def p1165 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1165 : zipCycle p1165 1 11 true (1) = true := by decide +kernel
theorem never1165 (m : Machine) (hm : compatible p1165 m) : NeverHalts m :=
  zipCycle_sound p1165 1 11 true (1) (by decide) cert1165 m hm
#print axioms never1165


/-- Third-level first-hole refinement 1166, 1RB---_1RC1LE_0RD0LC_1LD1RB_---0RC_------; entry 17, period 1. -/
def p1166 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1166 : zipCycle p1166 17 1 false (1) = true := by decide +kernel
theorem never1166 (m : Machine) (hm : compatible p1166 m) : NeverHalts m :=
  zipCycle_sound p1166 17 1 false (1) (by decide) cert1166 m hm
#print axioms never1166


/-- Third-level first-hole refinement 1167, 1RB---_1RC1LE_0RD1LC_1LD1RB_---0RC_------; entry 1, period 15. -/
def p1167 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1167 : zipCycle p1167 1 15 true (1) = true := by decide +kernel
theorem never1167 (m : Machine) (hm : compatible p1167 m) : NeverHalts m :=
  zipCycle_sound p1167 1 15 true (1) (by decide) cert1167 m hm
#print axioms never1167


/-- Third-level first-hole refinement 1168, 1RB---_1RC1LE_0RD0RC_1LD1RB_---0RC_------; entry 25, period 1. -/
def p1168 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1168 : zipCycle p1168 25 1 false (7) = true := by decide +kernel
theorem never1168 (m : Machine) (hm : compatible p1168 m) : NeverHalts m :=
  zipCycle_sound p1168 25 1 false (7) (by decide) cert1168 m hm
#print axioms never1168


/-- Third-level first-hole refinement 1169, 1RB---_1RC1LE_0RD1RC_1LD1RB_---0RC_------; entry 2, period 8. -/
def p1169 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1169 : zipCycle p1169 2 8 true (1) = true := by decide +kernel
theorem never1169 (m : Machine) (hm : compatible p1169 m) : NeverHalts m :=
  zipCycle_sound p1169 2 8 true (1) (by decide) cert1169 m hm
#print axioms never1169


/-- Third-level first-hole refinement 1170, 1RB---_1RC1LE_0RD0LD_1LD1RB_---0RC_------; entry 14, period 1. -/
def p1170 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1170 : zipCycle p1170 14 1 false (0) = true := by decide +kernel
theorem never1170 (m : Machine) (hm : compatible p1170 m) : NeverHalts m :=
  zipCycle_sound p1170 14 1 false (0) (by decide) cert1170 m hm
#print axioms never1170


/-- Third-level first-hole refinement 1171, 1RB---_1RC1LE_0RD1LD_1LD1RB_---0RC_------; entry 14, period 1. -/
def p1171 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1171 : zipCycle p1171 14 1 false (0) = true := by decide +kernel
theorem never1171 (m : Machine) (hm : compatible p1171 m) : NeverHalts m :=
  zipCycle_sound p1171 14 1 false (0) (by decide) cert1171 m hm
#print axioms never1171


/-- Third-level first-hole refinement 1172, 1RB---_1RC1LE_0RD0RD_1LD1RB_---0RC_------; entry 1, period 9. -/
def p1172 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1172 : zipCycle p1172 1 9 true (1) = true := by decide +kernel
theorem never1172 (m : Machine) (hm : compatible p1172 m) : NeverHalts m :=
  zipCycle_sound p1172 1 9 true (1) (by decide) cert1172 m hm
#print axioms never1172


/-- Third-level first-hole refinement 1173, 1RB---_1RC1LE_0RD1RD_1LD1RB_---0RC_------; entry 1, period 9. -/
def p1173 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1173 : zipCycle p1173 1 9 true (1) = true := by decide +kernel
theorem never1173 (m : Machine) (hm : compatible p1173 m) : NeverHalts m :=
  zipCycle_sound p1173 1 9 true (1) (by decide) cert1173 m hm
#print axioms never1173


/-- Third-level first-hole refinement 1174, 1RB---_1RC1LE_0RD1RB_1LD1RB_---1RC_------; entry 1, period 11. -/
def p1174 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1174 : zipCycle p1174 1 11 true (1) = true := by decide +kernel
theorem never1174 (m : Machine) (hm : compatible p1174 m) : NeverHalts m :=
  zipCycle_sound p1174 1 11 true (1) (by decide) cert1174 m hm
#print axioms never1174


/-- Third-level first-hole refinement 1175, 1RB---_1RC1LE_0RD0LC_1LD1RB_---1RC_------; entry 12, period 1. -/
def p1175 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1175 : zipCycle p1175 12 1 false (0) = true := by decide +kernel
theorem never1175 (m : Machine) (hm : compatible p1175 m) : NeverHalts m :=
  zipCycle_sound p1175 12 1 false (0) (by decide) cert1175 m hm
#print axioms never1175


/-- Third-level first-hole refinement 1176, 1RB---_1RC1LE_0RD1LC_1LD1RB_---1RC_------; entry 9, period 6. -/
def p1176 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1176 : zipCycle p1176 9 6 true (-1) = true := by decide +kernel
theorem never1176 (m : Machine) (hm : compatible p1176 m) : NeverHalts m :=
  zipCycle_sound p1176 9 6 true (-1) (by decide) cert1176 m hm
#print axioms never1176


/-- Third-level first-hole refinement 1177, 1RB---_1RC1LE_0RD1RC_1LD1RB_---1RC_------; entry 2, period 8. -/
def p1177 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1177 : zipCycle p1177 2 8 true (1) = true := by decide +kernel
theorem never1177 (m : Machine) (hm : compatible p1177 m) : NeverHalts m :=
  zipCycle_sound p1177 2 8 true (1) (by decide) cert1177 m hm
#print axioms never1177


/-- Third-level first-hole refinement 1178, 1RB---_1RC1LE_0RD0LD_1LD1RB_---1RC_------; entry 1, period 12. -/
def p1178 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1178 : zipCycle p1178 1 12 true (1) = true := by decide +kernel
theorem never1178 (m : Machine) (hm : compatible p1178 m) : NeverHalts m :=
  zipCycle_sound p1178 1 12 true (1) (by decide) cert1178 m hm
#print axioms never1178


/-- Third-level first-hole refinement 1179, 1RB---_1RC1LE_0RD1LD_1LD1RB_---1RC_------; entry 5, period 4. -/
def p1179 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1179 : zipCycle p1179 5 4 true (1) = true := by decide +kernel
theorem never1179 (m : Machine) (hm : compatible p1179 m) : NeverHalts m :=
  zipCycle_sound p1179 5 4 true (1) (by decide) cert1179 m hm
#print axioms never1179


/-- Third-level first-hole refinement 1180, 1RB---_1RC1LE_0RD0RD_1LD1RB_---1RC_------; entry 1, period 9. -/
def p1180 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1180 : zipCycle p1180 1 9 true (1) = true := by decide +kernel
theorem never1180 (m : Machine) (hm : compatible p1180 m) : NeverHalts m :=
  zipCycle_sound p1180 1 9 true (1) (by decide) cert1180 m hm
#print axioms never1180


/-- Third-level first-hole refinement 1181, 1RB---_1RC1LE_0RD1RD_1LD1RB_---1RC_------; entry 1, period 9. -/
def p1181 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1181 : zipCycle p1181 1 9 true (1) = true := by decide +kernel
theorem never1181 (m : Machine) (hm : compatible p1181 m) : NeverHalts m :=
  zipCycle_sound p1181 1 9 true (1) (by decide) cert1181 m hm
#print axioms never1181


/-- Third-level first-hole refinement 1182, 1RB---_1RC1LE_0RD0LE_1LD1RB_---1RC_------; entry 1, period 11. -/
def p1182 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1182 : zipCycle p1182 1 11 true (1) = true := by decide +kernel
theorem never1182 (m : Machine) (hm : compatible p1182 m) : NeverHalts m :=
  zipCycle_sound p1182 1 11 true (1) (by decide) cert1182 m hm
#print axioms never1182


/-- Third-level first-hole refinement 1183, 1RB---_1RC1LE_0RD1LE_1LD1RB_---1RC_------; entry 7, period 2. -/
def p1183 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1183 : zipCycle p1183 7 2 true (1) = true := by decide +kernel
theorem never1183 (m : Machine) (hm : compatible p1183 m) : NeverHalts m :=
  zipCycle_sound p1183 7 2 true (1) (by decide) cert1183 m hm
#print axioms never1183


/-- Third-level first-hole refinement 1184, 1RB---_1RC1LE_0RD0RE_1LD1RB_---1RC_------; entry 2, period 8. -/
def p1184 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1184 : zipCycle p1184 2 8 true (1) = true := by decide +kernel
theorem never1184 (m : Machine) (hm : compatible p1184 m) : NeverHalts m :=
  zipCycle_sound p1184 2 8 true (1) (by decide) cert1184 m hm
#print axioms never1184


/-- Third-level first-hole refinement 1185, 1RB---_1RC1LE_0RD1RE_1LD1RB_---1RC_------; entry 2, period 8. -/
def p1185 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1185 : zipCycle p1185 2 8 true (1) = true := by decide +kernel
theorem never1185 (m : Machine) (hm : compatible p1185 m) : NeverHalts m :=
  zipCycle_sound p1185 2 8 true (1) (by decide) cert1185 m hm
#print axioms never1185


/-- Third-level first-hole refinement 1186, 1RB---_1RC1LE_0RD0LB_1LD1RB_---0LD_------; entry 13, period 1. -/
def p1186 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1186 : zipCycle p1186 13 1 false (-1) = true := by decide +kernel
theorem never1186 (m : Machine) (hm : compatible p1186 m) : NeverHalts m :=
  zipCycle_sound p1186 13 1 false (-1) (by decide) cert1186 m hm
#print axioms never1186


/-- Third-level first-hole refinement 1187, 1RB---_1RC1LE_0RD1LB_1LD1RB_---0LD_------; entry 13, period 1. -/
def p1187 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1187 : zipCycle p1187 13 1 false (-1) = true := by decide +kernel
theorem never1187 (m : Machine) (hm : compatible p1187 m) : NeverHalts m :=
  zipCycle_sound p1187 13 1 false (-1) (by decide) cert1187 m hm
#print axioms never1187


/-- Third-level first-hole refinement 1188, 1RB---_1RC1LE_0RD1RB_1LD1RB_---0LD_------; entry 1, period 15. -/
def p1188 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1188 : zipCycle p1188 1 15 true (0) = true := by decide +kernel
theorem never1188 (m : Machine) (hm : compatible p1188 m) : NeverHalts m :=
  zipCycle_sound p1188 1 15 true (0) (by decide) cert1188 m hm
#print axioms never1188


/-- Third-level first-hole refinement 1189, 1RB---_1RC1LE_0RD0LC_1LD1RB_---0LD_------; entry 14, period 1. -/
def p1189 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1189 : zipCycle p1189 14 1 false (0) = true := by decide +kernel
theorem never1189 (m : Machine) (hm : compatible p1189 m) : NeverHalts m :=
  zipCycle_sound p1189 14 1 false (0) (by decide) cert1189 m hm
#print axioms never1189


/-- Third-level first-hole refinement 1190, 1RB---_1RC1LE_0RD1LC_1LD1RB_---0LD_------; entry 17, period 1. -/
def p1190 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1190 : zipCycle p1190 17 1 false (-1) = true := by decide +kernel
theorem never1190 (m : Machine) (hm : compatible p1190 m) : NeverHalts m :=
  zipCycle_sound p1190 17 1 false (-1) (by decide) cert1190 m hm
#print axioms never1190


/-- Third-level first-hole refinement 1191, 1RB---_1RC1LE_0RD1RC_1LD1RB_---0LD_------; entry 2, period 10. -/
def p1191 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1191 : zipCycle p1191 2 10 true (0) = true := by decide +kernel
theorem never1191 (m : Machine) (hm : compatible p1191 m) : NeverHalts m :=
  zipCycle_sound p1191 2 10 true (0) (by decide) cert1191 m hm
#print axioms never1191


/-- Third-level first-hole refinement 1192, 1RB---_1RC1LE_0RD0LD_1LD1RB_---0LD_------; entry 1, period 14. -/
def p1192 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1192 : zipCycle p1192 1 14 true (0) = true := by decide +kernel
theorem never1192 (m : Machine) (hm : compatible p1192 m) : NeverHalts m :=
  zipCycle_sound p1192 1 14 true (0) (by decide) cert1192 m hm
#print axioms never1192


/-- Third-level first-hole refinement 1193, 1RB---_1RC1LE_0RD1LD_1LD1RB_---0LD_------; entry 5, period 6. -/
def p1193 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1193 : zipCycle p1193 5 6 true (0) = true := by decide +kernel
theorem never1193 (m : Machine) (hm : compatible p1193 m) : NeverHalts m :=
  zipCycle_sound p1193 5 6 true (0) (by decide) cert1193 m hm
#print axioms never1193


/-- Third-level first-hole refinement 1194, 1RB---_1RC1LE_0RD0RD_1LD1RB_---0LD_------; entry 1, period 11. -/
def p1194 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1194 : zipCycle p1194 1 11 true (0) = true := by decide +kernel
theorem never1194 (m : Machine) (hm : compatible p1194 m) : NeverHalts m :=
  zipCycle_sound p1194 1 11 true (0) (by decide) cert1194 m hm
#print axioms never1194


/-- Third-level first-hole refinement 1195, 1RB---_1RC1LE_0RD1RD_1LD1RB_---0LD_------; entry 1, period 11. -/
def p1195 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1195 : zipCycle p1195 1 11 true (0) = true := by decide +kernel
theorem never1195 (m : Machine) (hm : compatible p1195 m) : NeverHalts m :=
  zipCycle_sound p1195 1 11 true (0) (by decide) cert1195 m hm
#print axioms never1195


/-- Third-level first-hole refinement 1196, 1RB---_1RC1LE_0RD0LE_1LD1RB_---0LD_------; entry 1, period 15. -/
def p1196 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1196 : zipCycle p1196 1 15 true (0) = true := by decide +kernel
theorem never1196 (m : Machine) (hm : compatible p1196 m) : NeverHalts m :=
  zipCycle_sound p1196 1 15 true (0) (by decide) cert1196 m hm
#print axioms never1196


/-- Third-level first-hole refinement 1197, 1RB---_1RC1LE_0RD1LE_1LD1RB_---0LD_------; entry 7, period 4. -/
def p1197 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1197 : zipCycle p1197 7 4 true (0) = true := by decide +kernel
theorem never1197 (m : Machine) (hm : compatible p1197 m) : NeverHalts m :=
  zipCycle_sound p1197 7 4 true (0) (by decide) cert1197 m hm
#print axioms never1197


/-- Third-level first-hole refinement 1198, 1RB---_1RC1LE_0RD1RE_1LD1RB_---0LD_------; entry 1, period 12. -/
def p1198 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1198 : zipCycle p1198 1 12 true (0) = true := by decide +kernel
theorem never1198 (m : Machine) (hm : compatible p1198 m) : NeverHalts m :=
  zipCycle_sound p1198 1 12 true (0) (by decide) cert1198 m hm
#print axioms never1198


/-- Third-level first-hole refinement 1199, 1RB---_1RC1LE_0RD---_1LD1RB_0LA0LE_------; entry 0, period 10. -/
def p1199 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1199 : zipCycle p1199 0 10 false (3) = true := by decide +kernel
theorem never1199 (m : Machine) (hm : compatible p1199 m) : NeverHalts m :=
  zipCycle_sound p1199 0 10 false (3) (by decide) cert1199 m hm
#print axioms never1199

end BB6.Agent24Raw45D3_11
