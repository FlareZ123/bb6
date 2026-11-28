import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_10
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1000, 1RB---_1RC0LE_0RD---_1LD1RB_1LD0LE_------; entry 10, period 1. -/
def p1000 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1000 : zipCycle p1000 10 1 false (-2) = true := by decide +kernel
theorem never1000 (m : Machine) (hm : compatible p1000 m) : NeverHalts m :=
  zipCycle_sound p1000 10 1 false (-2) (by decide) cert1000 m hm
#print axioms never1000


/-- Third-level first-hole refinement 1001, 1RB---_1RC0LE_0RD---_1LD1RB_0RD0LE_------; entry 10, period 1. -/
def p1001 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1001 : zipCycle p1001 10 1 false (0) = true := by decide +kernel
theorem never1001 (m : Machine) (hm : compatible p1001 m) : NeverHalts m :=
  zipCycle_sound p1001 10 1 false (0) (by decide) cert1001 m hm
#print axioms never1001


/-- Third-level first-hole refinement 1002, 1RB---_1RC0LE_0RD---_1LD1RB_1RD0LE_------; entry 8, period 5. -/
def p1002 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1002 : zipCycle p1002 8 5 false (0) = true := by decide +kernel
theorem never1002 (m : Machine) (hm : compatible p1002 m) : NeverHalts m :=
  zipCycle_sound p1002 8 5 false (0) (by decide) cert1002 m hm
#print axioms never1002


/-- Third-level first-hole refinement 1003, 1RB---_1RC0LE_0RD---_1LD1RB_0LE0LE_------; entry 9, period 1. -/
def p1003 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1003 : zipCycle p1003 9 1 false (-1) = true := by decide +kernel
theorem never1003 (m : Machine) (hm : compatible p1003 m) : NeverHalts m :=
  zipCycle_sound p1003 9 1 false (-1) (by decide) cert1003 m hm
#print axioms never1003


/-- Third-level first-hole refinement 1004, 1RB---_1RC0LE_0RD---_1LD1RB_1LE0LE_------; entry 9, period 1. -/
def p1004 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1004 : zipCycle p1004 9 1 false (-1) = true := by decide +kernel
theorem never1004 (m : Machine) (hm : compatible p1004 m) : NeverHalts m :=
  zipCycle_sound p1004 9 1 false (-1) (by decide) cert1004 m hm
#print axioms never1004


/-- Third-level first-hole refinement 1005, 1RB---_1RC0LE_0RD---_1LD1RB_0RE0LE_------; entry 14, period 1. -/
def p1005 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1005 : zipCycle p1005 14 1 true (2) = true := by decide +kernel
theorem never1005 (m : Machine) (hm : compatible p1005 m) : NeverHalts m :=
  zipCycle_sound p1005 14 1 true (2) (by decide) cert1005 m hm
#print axioms never1005


/-- Third-level first-hole refinement 1006, 1RB---_1RC0LE_0RD---_1LD1RB_1RE0LE_------; entry 18, period 1. -/
def p1006 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1006 : zipCycle p1006 18 1 true (-2) = true := by decide +kernel
theorem never1006 (m : Machine) (hm : compatible p1006 m) : NeverHalts m :=
  zipCycle_sound p1006 18 1 true (-2) (by decide) cert1006 m hm
#print axioms never1006


/-- Third-level first-hole refinement 1007, 1RB---_1RC0LE_0RD---_1LD1RB_1LA1LE_------; entry 8, period 4. -/
def p1007 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1007 : zipCycle p1007 8 4 false (0) = true := by decide +kernel
theorem never1007 (m : Machine) (hm : compatible p1007 m) : NeverHalts m :=
  zipCycle_sound p1007 8 4 false (0) (by decide) cert1007 m hm
#print axioms never1007


/-- Third-level first-hole refinement 1008, 1RB---_1RC0LE_0RD---_1LD1RB_1RB1LE_------; entry 8, period 3. -/
def p1008 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1008 : zipCycle p1008 8 3 false (0) = true := by decide +kernel
theorem never1008 (m : Machine) (hm : compatible p1008 m) : NeverHalts m :=
  zipCycle_sound p1008 8 3 false (0) (by decide) cert1008 m hm
#print axioms never1008


/-- Third-level first-hole refinement 1009, 1RB---_1RC0LE_0RD---_1LD1RB_0LC1LE_------; entry 11, period 1. -/
def p1009 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1009 : zipCycle p1009 11 1 false (-1) = true := by decide +kernel
theorem never1009 (m : Machine) (hm : compatible p1009 m) : NeverHalts m :=
  zipCycle_sound p1009 11 1 false (-1) (by decide) cert1009 m hm
#print axioms never1009


/-- Third-level first-hole refinement 1010, 1RB---_1RC0LE_0RD---_1LD1RB_1LC1LE_------; entry 8, period 5. -/
def p1010 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1010 : zipCycle p1010 8 5 false (0) = true := by decide +kernel
theorem never1010 (m : Machine) (hm : compatible p1010 m) : NeverHalts m :=
  zipCycle_sound p1010 8 5 false (0) (by decide) cert1010 m hm
#print axioms never1010


/-- Third-level first-hole refinement 1011, 1RB---_1RC0LE_0RD---_1LD1RB_0LD1LE_------; entry 10, period 1. -/
def p1011 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1011 : zipCycle p1011 10 1 false (-2) = true := by decide +kernel
theorem never1011 (m : Machine) (hm : compatible p1011 m) : NeverHalts m :=
  zipCycle_sound p1011 10 1 false (-2) (by decide) cert1011 m hm
#print axioms never1011


/-- Third-level first-hole refinement 1012, 1RB---_1RC0LE_0RD---_1LD1RB_1LD1LE_------; entry 10, period 1. -/
def p1012 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1012 : zipCycle p1012 10 1 false (-2) = true := by decide +kernel
theorem never1012 (m : Machine) (hm : compatible p1012 m) : NeverHalts m :=
  zipCycle_sound p1012 10 1 false (-2) (by decide) cert1012 m hm
#print axioms never1012


/-- Third-level first-hole refinement 1013, 1RB---_1RC0LE_0RD---_1LD1RB_0RD1LE_------; entry 1, period 17. -/
def p1013 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1013 : zipCycle p1013 1 17 true (-1) = true := by decide +kernel
theorem never1013 (m : Machine) (hm : compatible p1013 m) : NeverHalts m :=
  zipCycle_sound p1013 1 17 true (-1) (by decide) cert1013 m hm
#print axioms never1013


/-- Third-level first-hole refinement 1014, 1RB---_1RC0LE_0RD---_1LD1RB_1RD1LE_------; entry 5, period 5. -/
def p1014 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1014 : zipCycle p1014 5 5 false (2) = true := by decide +kernel
theorem never1014 (m : Machine) (hm : compatible p1014 m) : NeverHalts m :=
  zipCycle_sound p1014 5 5 false (2) (by decide) cert1014 m hm
#print axioms never1014


/-- Third-level first-hole refinement 1015, 1RB---_1RC0LE_0RD---_1LD1RB_0LE1LE_------; entry 9, period 1. -/
def p1015 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1015 : zipCycle p1015 9 1 false (-1) = true := by decide +kernel
theorem never1015 (m : Machine) (hm : compatible p1015 m) : NeverHalts m :=
  zipCycle_sound p1015 9 1 false (-1) (by decide) cert1015 m hm
#print axioms never1015


/-- Third-level first-hole refinement 1016, 1RB---_1RC0LE_0RD---_1LD1RB_1LE1LE_------; entry 9, period 1. -/
def p1016 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1016 : zipCycle p1016 9 1 false (-1) = true := by decide +kernel
theorem never1016 (m : Machine) (hm : compatible p1016 m) : NeverHalts m :=
  zipCycle_sound p1016 9 1 false (-1) (by decide) cert1016 m hm
#print axioms never1016


/-- Third-level first-hole refinement 1017, 1RB---_1RC0LE_0RD---_1LD1RB_0RE1LE_------; entry 8, period 2. -/
def p1017 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1017 : zipCycle p1017 8 2 true (-1) = true := by decide +kernel
theorem never1017 (m : Machine) (hm : compatible p1017 m) : NeverHalts m :=
  zipCycle_sound p1017 8 2 true (-1) (by decide) cert1017 m hm
#print axioms never1017


/-- Third-level first-hole refinement 1018, 1RB---_1RC0LE_0RD---_1LD1RB_1RE1LE_------; entry 7, period 3. -/
def p1018 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1018 : zipCycle p1018 7 3 false (1) = true := by decide +kernel
theorem never1018 (m : Machine) (hm : compatible p1018 m) : NeverHalts m :=
  zipCycle_sound p1018 7 3 false (1) (by decide) cert1018 m hm
#print axioms never1018


/-- Third-level first-hole refinement 1019, 1RB---_1RC0LE_0RD---_1LD1RB_1LA0RE_------; entry 6, period 4. -/
def p1019 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1019 : zipCycle p1019 6 4 true (1) = true := by decide +kernel
theorem never1019 (m : Machine) (hm : compatible p1019 m) : NeverHalts m :=
  zipCycle_sound p1019 6 4 true (1) (by decide) cert1019 m hm
#print axioms never1019


/-- Third-level first-hole refinement 1020, 1RB---_1RC0LE_0RD---_1LD1RB_0LB0RE_------; entry 1, period 11. -/
def p1020 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1020 : zipCycle p1020 1 11 true (1) = true := by decide +kernel
theorem never1020 (m : Machine) (hm : compatible p1020 m) : NeverHalts m :=
  zipCycle_sound p1020 1 11 true (1) (by decide) cert1020 m hm
#print axioms never1020


/-- Third-level first-hole refinement 1021, 1RB---_1RC0LE_0RD---_1LD1RB_0RB0RE_------; entry 1, period 10. -/
def p1021 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1021 : zipCycle p1021 1 10 true (1) = true := by decide +kernel
theorem never1021 (m : Machine) (hm : compatible p1021 m) : NeverHalts m :=
  zipCycle_sound p1021 1 10 true (1) (by decide) cert1021 m hm
#print axioms never1021


/-- Third-level first-hole refinement 1022, 1RB---_1RC0LE_0RD---_1LD1RB_1RB0RE_------; entry 1, period 11. -/
def p1022 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1022 : zipCycle p1022 1 11 true (1) = true := by decide +kernel
theorem never1022 (m : Machine) (hm : compatible p1022 m) : NeverHalts m :=
  zipCycle_sound p1022 1 11 true (1) (by decide) cert1022 m hm
#print axioms never1022


/-- Third-level first-hole refinement 1023, 1RB---_1RC0LE_0RD---_1LD1RB_0LC0RE_------; entry 17, period 1. -/
def p1023 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1023 : zipCycle p1023 17 1 false (1) = true := by decide +kernel
theorem never1023 (m : Machine) (hm : compatible p1023 m) : NeverHalts m :=
  zipCycle_sound p1023 17 1 false (1) (by decide) cert1023 m hm
#print axioms never1023


/-- Third-level first-hole refinement 1024, 1RB---_1RC0LE_0RD---_1LD1RB_1LC0RE_------; entry 1, period 15. -/
def p1024 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1024 : zipCycle p1024 1 15 true (1) = true := by decide +kernel
theorem never1024 (m : Machine) (hm : compatible p1024 m) : NeverHalts m :=
  zipCycle_sound p1024 1 15 true (1) (by decide) cert1024 m hm
#print axioms never1024


/-- Third-level first-hole refinement 1025, 1RB---_1RC0LE_0RD---_1LD1RB_0LD0RE_------; entry 14, period 1. -/
def p1025 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1025 : zipCycle p1025 14 1 false (0) = true := by decide +kernel
theorem never1025 (m : Machine) (hm : compatible p1025 m) : NeverHalts m :=
  zipCycle_sound p1025 14 1 false (0) (by decide) cert1025 m hm
#print axioms never1025


/-- Third-level first-hole refinement 1026, 1RB---_1RC0LE_0RD---_1LD1RB_1LD0RE_------; entry 14, period 1. -/
def p1026 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1026 : zipCycle p1026 14 1 false (0) = true := by decide +kernel
theorem never1026 (m : Machine) (hm : compatible p1026 m) : NeverHalts m :=
  zipCycle_sound p1026 14 1 false (0) (by decide) cert1026 m hm
#print axioms never1026


/-- Third-level first-hole refinement 1027, 1RB---_1RC0LE_0RD---_1LD1RB_0RD0RE_------; entry 1, period 9. -/
def p1027 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1027 : zipCycle p1027 1 9 true (1) = true := by decide +kernel
theorem never1027 (m : Machine) (hm : compatible p1027 m) : NeverHalts m :=
  zipCycle_sound p1027 1 9 true (1) (by decide) cert1027 m hm
#print axioms never1027


/-- Third-level first-hole refinement 1028, 1RB---_1RC0LE_0RD---_1LD1RB_1RD0RE_------; entry 1, period 9. -/
def p1028 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1028 : zipCycle p1028 1 9 true (1) = true := by decide +kernel
theorem never1028 (m : Machine) (hm : compatible p1028 m) : NeverHalts m :=
  zipCycle_sound p1028 1 9 true (1) (by decide) cert1028 m hm
#print axioms never1028


/-- Third-level first-hole refinement 1029, 1RB---_1RC0LE_0RD---_1LD1RB_0LE0RE_------; entry 11, period 1. -/
def p1029 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1029 : zipCycle p1029 11 1 false (1) = true := by decide +kernel
theorem never1029 (m : Machine) (hm : compatible p1029 m) : NeverHalts m :=
  zipCycle_sound p1029 11 1 false (1) (by decide) cert1029 m hm
#print axioms never1029


/-- Third-level first-hole refinement 1030, 1RB---_1RC0LE_0RD---_1LD1RB_1LE0RE_------; entry 14, period 1. -/
def p1030 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1030 : zipCycle p1030 14 1 false (4) = true := by decide +kernel
theorem never1030 (m : Machine) (hm : compatible p1030 m) : NeverHalts m :=
  zipCycle_sound p1030 14 1 false (4) (by decide) cert1030 m hm
#print axioms never1030


/-- Third-level first-hole refinement 1031, 1RB---_1RC0LE_0RD---_1LD1RB_0RE0RE_------; entry 10, period 1. -/
def p1031 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1031 : zipCycle p1031 10 1 true (4) = true := by decide +kernel
theorem never1031 (m : Machine) (hm : compatible p1031 m) : NeverHalts m :=
  zipCycle_sound p1031 10 1 true (4) (by decide) cert1031 m hm
#print axioms never1031


/-- Third-level first-hole refinement 1032, 1RB---_1RC0LE_0RD---_1LD1RB_1RE0RE_------; entry 10, period 1. -/
def p1032 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1032 : zipCycle p1032 10 1 true (4) = true := by decide +kernel
theorem never1032 (m : Machine) (hm : compatible p1032 m) : NeverHalts m :=
  zipCycle_sound p1032 10 1 true (4) (by decide) cert1032 m hm
#print axioms never1032


/-- Third-level first-hole refinement 1033, 1RB---_1RC0LE_0RD---_1LD1RB_0LB1RE_------; entry 9, period 10. -/
def p1033 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1033 : zipCycle p1033 9 10 false (1) = true := by decide +kernel
theorem never1033 (m : Machine) (hm : compatible p1033 m) : NeverHalts m :=
  zipCycle_sound p1033 9 10 false (1) (by decide) cert1033 m hm
#print axioms never1033


/-- Third-level first-hole refinement 1034, 1RB---_1RC0LE_0RD---_1LD1RB_0RB1RE_------; entry 1, period 10. -/
def p1034 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1034 : zipCycle p1034 1 10 true (1) = true := by decide +kernel
theorem never1034 (m : Machine) (hm : compatible p1034 m) : NeverHalts m :=
  zipCycle_sound p1034 1 10 true (1) (by decide) cert1034 m hm
#print axioms never1034


/-- Third-level first-hole refinement 1035, 1RB---_1RC0LE_0RD---_1LD1RB_1RB1RE_------; entry 1, period 11. -/
def p1035 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1035 : zipCycle p1035 1 11 true (1) = true := by decide +kernel
theorem never1035 (m : Machine) (hm : compatible p1035 m) : NeverHalts m :=
  zipCycle_sound p1035 1 11 true (1) (by decide) cert1035 m hm
#print axioms never1035


/-- Third-level first-hole refinement 1036, 1RB---_1RC0LE_0RD---_1LD1RB_1LD1RE_------; entry 5, period 4. -/
def p1036 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1036 : zipCycle p1036 5 4 true (1) = true := by decide +kernel
theorem never1036 (m : Machine) (hm : compatible p1036 m) : NeverHalts m :=
  zipCycle_sound p1036 5 4 true (1) (by decide) cert1036 m hm
#print axioms never1036


/-- Third-level first-hole refinement 1037, 1RB---_1RC0LE_0RD---_1LD1RB_0RD1RE_------; entry 1, period 9. -/
def p1037 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1037 : zipCycle p1037 1 9 true (1) = true := by decide +kernel
theorem never1037 (m : Machine) (hm : compatible p1037 m) : NeverHalts m :=
  zipCycle_sound p1037 1 9 true (1) (by decide) cert1037 m hm
#print axioms never1037


/-- Third-level first-hole refinement 1038, 1RB---_1RC0LE_0RD---_1LD1RB_1RD1RE_------; entry 1, period 9. -/
def p1038 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1038 : zipCycle p1038 1 9 true (1) = true := by decide +kernel
theorem never1038 (m : Machine) (hm : compatible p1038 m) : NeverHalts m :=
  zipCycle_sound p1038 1 9 true (1) (by decide) cert1038 m hm
#print axioms never1038


/-- Third-level first-hole refinement 1039, 1RB---_1RC0LE_0RD---_1LD1RB_0LE1RE_------; entry 7, period 2. -/
def p1039 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1039 : zipCycle p1039 7 2 true (1) = true := by decide +kernel
theorem never1039 (m : Machine) (hm : compatible p1039 m) : NeverHalts m :=
  zipCycle_sound p1039 7 2 true (1) (by decide) cert1039 m hm
#print axioms never1039


/-- Third-level first-hole refinement 1040, 1RB---_1RC0LE_0RD---_1LD1RB_1LE1RE_------; entry 10, period 3. -/
def p1040 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1040 : zipCycle p1040 10 3 true (2) = true := by decide +kernel
theorem never1040 (m : Machine) (hm : compatible p1040 m) : NeverHalts m :=
  zipCycle_sound p1040 10 3 true (2) (by decide) cert1040 m hm
#print axioms never1040


/-- Third-level first-hole refinement 1041, 1RB---_1RC0LE_0RD---_1LD1RB_0RE1RE_------; entry 10, period 1. -/
def p1041 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1041 : zipCycle p1041 10 1 true (4) = true := by decide +kernel
theorem never1041 (m : Machine) (hm : compatible p1041 m) : NeverHalts m :=
  zipCycle_sound p1041 10 1 true (4) (by decide) cert1041 m hm
#print axioms never1041


/-- Third-level first-hole refinement 1042, 1RB---_1RC0LE_0RD---_1LD1RB_1RE1RE_------; entry 10, period 1. -/
def p1042 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1042 : zipCycle p1042 10 1 true (4) = true := by decide +kernel
theorem never1042 (m : Machine) (hm : compatible p1042 m) : NeverHalts m :=
  zipCycle_sound p1042 10 1 true (4) (by decide) cert1042 m hm
#print axioms never1042


/-- Third-level first-hole refinement 1043, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---0LA; entry 0, period 9. -/
def p1043 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1043 : zipCycle p1043 0 9 false (3) = true := by decide +kernel
theorem never1043 (m : Machine) (hm : compatible p1043 m) : NeverHalts m :=
  zipCycle_sound p1043 0 9 false (3) (by decide) cert1043 m hm
#print axioms never1043


/-- Third-level first-hole refinement 1044, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---0RB; entry 1, period 11. -/
def p1044 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1044 : zipCycle p1044 1 11 true (0) = true := by decide +kernel
theorem never1044 (m : Machine) (hm : compatible p1044 m) : NeverHalts m :=
  zipCycle_sound p1044 1 11 true (0) (by decide) cert1044 m hm
#print axioms never1044


/-- Third-level first-hole refinement 1045, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---1RB; entry 1, period 11. -/
def p1045 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1045 : zipCycle p1045 1 11 true (0) = true := by decide +kernel
theorem never1045 (m : Machine) (hm : compatible p1045 m) : NeverHalts m :=
  zipCycle_sound p1045 1 11 true (0) (by decide) cert1045 m hm
#print axioms never1045


/-- Third-level first-hole refinement 1046, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---0LC; entry 10, period 1. -/
def p1046 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1046 : zipCycle p1046 10 1 false (0) = true := by decide +kernel
theorem never1046 (m : Machine) (hm : compatible p1046 m) : NeverHalts m :=
  zipCycle_sound p1046 10 1 false (0) (by decide) cert1046 m hm
#print axioms never1046


/-- Third-level first-hole refinement 1047, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---1LC; entry 1, period 13. -/
def p1047 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1047 : zipCycle p1047 1 13 true (-1) = true := by decide +kernel
theorem never1047 (m : Machine) (hm : compatible p1047 m) : NeverHalts m :=
  zipCycle_sound p1047 1 13 true (-1) (by decide) cert1047 m hm
#print axioms never1047


/-- Third-level first-hole refinement 1048, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---0RC; entry 10, period 1. -/
def p1048 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1048 : zipCycle p1048 10 1 false (2) = true := by decide +kernel
theorem never1048 (m : Machine) (hm : compatible p1048 m) : NeverHalts m :=
  zipCycle_sound p1048 10 1 false (2) (by decide) cert1048 m hm
#print axioms never1048


/-- Third-level first-hole refinement 1049, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---0LD; entry 9, period 1. -/
def p1049 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1049 : zipCycle p1049 9 1 false (-1) = true := by decide +kernel
theorem never1049 (m : Machine) (hm : compatible p1049 m) : NeverHalts m :=
  zipCycle_sound p1049 9 1 false (-1) (by decide) cert1049 m hm
#print axioms never1049


/-- Third-level first-hole refinement 1050, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---1LD; entry 9, period 1. -/
def p1050 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1050 : zipCycle p1050 9 1 false (-1) = true := by decide +kernel
theorem never1050 (m : Machine) (hm : compatible p1050 m) : NeverHalts m :=
  zipCycle_sound p1050 9 1 false (-1) (by decide) cert1050 m hm
#print axioms never1050


/-- Third-level first-hole refinement 1051, 1RB---_1RC0LE_0RD---_1LD1RB_---0LF_---0RD; entry 9, period 1. -/
def p1051 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1051 : zipCycle p1051 9 1 false (1) = true := by decide +kernel
theorem never1051 (m : Machine) (hm : compatible p1051 m) : NeverHalts m :=
  zipCycle_sound p1051 9 1 false (1) (by decide) cert1051 m hm
#print axioms never1051


/-- Third-level first-hole refinement 1052, 1RB---_1RC0LE_0RD---_1LD1RB_---1LF_---0LC; entry 10, period 1. -/
def p1052 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1052 : zipCycle p1052 10 1 false (0) = true := by decide +kernel
theorem never1052 (m : Machine) (hm : compatible p1052 m) : NeverHalts m :=
  zipCycle_sound p1052 10 1 false (0) (by decide) cert1052 m hm
#print axioms never1052


/-- Third-level first-hole refinement 1053, 1RB---_1RC0LE_0RD---_1LD1RB_---1LF_---0LD; entry 9, period 1. -/
def p1053 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1053 : zipCycle p1053 9 1 false (-1) = true := by decide +kernel
theorem never1053 (m : Machine) (hm : compatible p1053 m) : NeverHalts m :=
  zipCycle_sound p1053 9 1 false (-1) (by decide) cert1053 m hm
#print axioms never1053


/-- Third-level first-hole refinement 1054, 1RB---_1RC0LE_0RD---_1LD1RB_---1LF_---1LD; entry 9, period 1. -/
def p1054 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1054 : zipCycle p1054 9 1 false (-1) = true := by decide +kernel
theorem never1054 (m : Machine) (hm : compatible p1054 m) : NeverHalts m :=
  zipCycle_sound p1054 9 1 false (-1) (by decide) cert1054 m hm
#print axioms never1054


/-- Third-level first-hole refinement 1055, 1RB---_1RC0LE_0RD---_1LD1RB_---1LF_---1RE; entry 7, period 2. -/
def p1055 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1055 : zipCycle p1055 7 2 true (0) = true := by decide +kernel
theorem never1055 (m : Machine) (hm : compatible p1055 m) : NeverHalts m :=
  zipCycle_sound p1055 7 2 true (0) (by decide) cert1055 m hm
#print axioms never1055


/-- Third-level first-hole refinement 1056, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_1LA---; entry 6, period 4. -/
def p1056 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1056 : zipCycle p1056 6 4 true (1) = true := by decide +kernel
theorem never1056 (m : Machine) (hm : compatible p1056 m) : NeverHalts m :=
  zipCycle_sound p1056 6 4 true (1) (by decide) cert1056 m hm
#print axioms never1056


/-- Third-level first-hole refinement 1057, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_0LB---; entry 1, period 11. -/
def p1057 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1057 : zipCycle p1057 1 11 true (1) = true := by decide +kernel
theorem never1057 (m : Machine) (hm : compatible p1057 m) : NeverHalts m :=
  zipCycle_sound p1057 1 11 true (1) (by decide) cert1057 m hm
#print axioms never1057


/-- Third-level first-hole refinement 1058, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_1RB---; entry 1, period 11. -/
def p1058 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1058 : zipCycle p1058 1 11 true (1) = true := by decide +kernel
theorem never1058 (m : Machine) (hm : compatible p1058 m) : NeverHalts m :=
  zipCycle_sound p1058 1 11 true (1) (by decide) cert1058 m hm
#print axioms never1058


/-- Third-level first-hole refinement 1059, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_0LC---; entry 17, period 1. -/
def p1059 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1059 : zipCycle p1059 17 1 false (1) = true := by decide +kernel
theorem never1059 (m : Machine) (hm : compatible p1059 m) : NeverHalts m :=
  zipCycle_sound p1059 17 1 false (1) (by decide) cert1059 m hm
#print axioms never1059


/-- Third-level first-hole refinement 1060, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_1LC---; entry 1, period 15. -/
def p1060 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1060 : zipCycle p1060 1 15 true (1) = true := by decide +kernel
theorem never1060 (m : Machine) (hm : compatible p1060 m) : NeverHalts m :=
  zipCycle_sound p1060 1 15 true (1) (by decide) cert1060 m hm
#print axioms never1060


/-- Third-level first-hole refinement 1061, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_0LD---; entry 14, period 1. -/
def p1061 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1061 : zipCycle p1061 14 1 false (0) = true := by decide +kernel
theorem never1061 (m : Machine) (hm : compatible p1061 m) : NeverHalts m :=
  zipCycle_sound p1061 14 1 false (0) (by decide) cert1061 m hm
#print axioms never1061


/-- Third-level first-hole refinement 1062, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_1LD---; entry 14, period 1. -/
def p1062 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1062 : zipCycle p1062 14 1 false (0) = true := by decide +kernel
theorem never1062 (m : Machine) (hm : compatible p1062 m) : NeverHalts m :=
  zipCycle_sound p1062 14 1 false (0) (by decide) cert1062 m hm
#print axioms never1062


/-- Third-level first-hole refinement 1063, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_0RD---; entry 1, period 9. -/
def p1063 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1063 : zipCycle p1063 1 9 true (1) = true := by decide +kernel
theorem never1063 (m : Machine) (hm : compatible p1063 m) : NeverHalts m :=
  zipCycle_sound p1063 1 9 true (1) (by decide) cert1063 m hm
#print axioms never1063


/-- Third-level first-hole refinement 1064, 1RB---_1RC0LE_0RD---_1LD1RB_---0RF_1RD---; entry 1, period 9. -/
def p1064 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1064 : zipCycle p1064 1 9 true (1) = true := by decide +kernel
theorem never1064 (m : Machine) (hm : compatible p1064 m) : NeverHalts m :=
  zipCycle_sound p1064 1 9 true (1) (by decide) cert1064 m hm
#print axioms never1064


/-- Third-level first-hole refinement 1065, 1RB---_1RC0LE_0RD---_1LD1RB_---1RF_1RB---; entry 1, period 11. -/
def p1065 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1065 : zipCycle p1065 1 11 true (1) = true := by decide +kernel
theorem never1065 (m : Machine) (hm : compatible p1065 m) : NeverHalts m :=
  zipCycle_sound p1065 1 11 true (1) (by decide) cert1065 m hm
#print axioms never1065


/-- Third-level first-hole refinement 1066, 1RB---_1RC0LE_0RD---_1LD1RB_---1RF_1LD---; entry 5, period 4. -/
def p1066 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1066 : zipCycle p1066 5 4 true (1) = true := by decide +kernel
theorem never1066 (m : Machine) (hm : compatible p1066 m) : NeverHalts m :=
  zipCycle_sound p1066 5 4 true (1) (by decide) cert1066 m hm
#print axioms never1066


/-- Third-level first-hole refinement 1067, 1RB---_1RC0LE_0RD---_1LD1RB_---1RF_0RD---; entry 1, period 9. -/
def p1067 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1067 : zipCycle p1067 1 9 true (1) = true := by decide +kernel
theorem never1067 (m : Machine) (hm : compatible p1067 m) : NeverHalts m :=
  zipCycle_sound p1067 1 9 true (1) (by decide) cert1067 m hm
#print axioms never1067


/-- Third-level first-hole refinement 1068, 1RB---_1RC0LE_0RD---_1LD1RB_---1RF_1RD---; entry 1, period 9. -/
def p1068 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1068 : zipCycle p1068 1 9 true (1) = true := by decide +kernel
theorem never1068 (m : Machine) (hm : compatible p1068 m) : NeverHalts m :=
  zipCycle_sound p1068 1 9 true (1) (by decide) cert1068 m hm
#print axioms never1068


/-- Third-level first-hole refinement 1069, 1RB---_1RC0LE_0RD---_1LD1RB_---1RF_0LE---; entry 7, period 2. -/
def p1069 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1069 : zipCycle p1069 7 2 true (1) = true := by decide +kernel
theorem never1069 (m : Machine) (hm : compatible p1069 m) : NeverHalts m :=
  zipCycle_sound p1069 7 2 true (1) (by decide) cert1069 m hm
#print axioms never1069


/-- Third-level first-hole refinement 1070, 1RB1RA_1RC1LE_0RD---_1LD1RB_---0LA_------; entry 6, period 4. -/
def p1070 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1070 : zipCycle p1070 6 4 true (0) = true := by decide +kernel
theorem never1070 (m : Machine) (hm : compatible p1070 m) : NeverHalts m :=
  zipCycle_sound p1070 6 4 true (0) (by decide) cert1070 m hm
#print axioms never1070


/-- Third-level first-hole refinement 1071, 1RB0LC_1RC1LE_0RD---_1LD1RB_---0LA_------; entry 10, period 1. -/
def p1071 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1071 : zipCycle p1071 10 1 false (0) = true := by decide +kernel
theorem never1071 (m : Machine) (hm : compatible p1071 m) : NeverHalts m :=
  zipCycle_sound p1071 10 1 false (0) (by decide) cert1071 m hm
#print axioms never1071


/-- Third-level first-hole refinement 1072, 1RB0LD_1RC1LE_0RD---_1LD1RB_---0LA_------; entry 9, period 1. -/
def p1072 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1072 : zipCycle p1072 9 1 false (-1) = true := by decide +kernel
theorem never1072 (m : Machine) (hm : compatible p1072 m) : NeverHalts m :=
  zipCycle_sound p1072 9 1 false (-1) (by decide) cert1072 m hm
#print axioms never1072


/-- Third-level first-hole refinement 1073, 1RB1LD_1RC1LE_0RD---_1LD1RB_---0LA_------; entry 9, period 1. -/
def p1073 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1073 : zipCycle p1073 9 1 false (-1) = true := by decide +kernel
theorem never1073 (m : Machine) (hm : compatible p1073 m) : NeverHalts m :=
  zipCycle_sound p1073 9 1 false (-1) (by decide) cert1073 m hm
#print axioms never1073


/-- Third-level first-hole refinement 1074, 1RB0RD_1RC1LE_0RD---_1LD1RB_---0LA_------; entry 9, period 1. -/
def p1074 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1074 : zipCycle p1074 9 1 false (1) = true := by decide +kernel
theorem never1074 (m : Machine) (hm : compatible p1074 m) : NeverHalts m :=
  zipCycle_sound p1074 9 1 false (1) (by decide) cert1074 m hm
#print axioms never1074


/-- Third-level first-hole refinement 1075, 1RB1LA_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 9, period 3. -/
def p1075 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1075 : zipCycle p1075 9 3 false (0) = true := by decide +kernel
theorem never1075 (m : Machine) (hm : compatible p1075 m) : NeverHalts m :=
  zipCycle_sound p1075 9 3 false (0) (by decide) cert1075 m hm
#print axioms never1075


/-- Third-level first-hole refinement 1076, 1RB0RA_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 0, period 12. -/
def p1076 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1076 : zipCycle p1076 0 12 true (0) = true := by decide +kernel
theorem never1076 (m : Machine) (hm : compatible p1076 m) : NeverHalts m :=
  zipCycle_sound p1076 0 12 true (0) (by decide) cert1076 m hm
#print axioms never1076


/-- Third-level first-hole refinement 1077, 1RB1RA_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 0, period 12. -/
def p1077 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1077 : zipCycle p1077 0 12 true (0) = true := by decide +kernel
theorem never1077 (m : Machine) (hm : compatible p1077 m) : NeverHalts m :=
  zipCycle_sound p1077 0 12 true (0) (by decide) cert1077 m hm
#print axioms never1077


/-- Third-level first-hole refinement 1078, 1RB0LB_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 6, period 9. -/
def p1078 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1078 : zipCycle p1078 6 9 false (2) = true := by decide +kernel
theorem never1078 (m : Machine) (hm : compatible p1078 m) : NeverHalts m :=
  zipCycle_sound p1078 6 9 false (2) (by decide) cert1078 m hm
#print axioms never1078


/-- Third-level first-hole refinement 1079, 1RB1RB_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 9, period 3. -/
def p1079 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1079 : zipCycle p1079 9 3 false (1) = true := by decide +kernel
theorem never1079 (m : Machine) (hm : compatible p1079 m) : NeverHalts m :=
  zipCycle_sound p1079 9 3 false (1) (by decide) cert1079 m hm
#print axioms never1079


/-- Third-level first-hole refinement 1080, 1RB0LC_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 10, period 1. -/
def p1080 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1080 : zipCycle p1080 10 1 false (0) = true := by decide +kernel
theorem never1080 (m : Machine) (hm : compatible p1080 m) : NeverHalts m :=
  zipCycle_sound p1080 10 1 false (0) (by decide) cert1080 m hm
#print axioms never1080


/-- Third-level first-hole refinement 1081, 1RB1LC_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 11, period 3. -/
def p1081 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1081 : zipCycle p1081 11 3 false (1) = true := by decide +kernel
theorem never1081 (m : Machine) (hm : compatible p1081 m) : NeverHalts m :=
  zipCycle_sound p1081 11 3 false (1) (by decide) cert1081 m hm
#print axioms never1081


/-- Third-level first-hole refinement 1082, 1RB0LD_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 9, period 1. -/
def p1082 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1082 : zipCycle p1082 9 1 false (-1) = true := by decide +kernel
theorem never1082 (m : Machine) (hm : compatible p1082 m) : NeverHalts m :=
  zipCycle_sound p1082 9 1 false (-1) (by decide) cert1082 m hm
#print axioms never1082


/-- Third-level first-hole refinement 1083, 1RB1LD_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 9, period 1. -/
def p1083 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1083 : zipCycle p1083 9 1 false (-1) = true := by decide +kernel
theorem never1083 (m : Machine) (hm : compatible p1083 m) : NeverHalts m :=
  zipCycle_sound p1083 9 1 false (-1) (by decide) cert1083 m hm
#print axioms never1083


/-- Third-level first-hole refinement 1084, 1RB0RD_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 10, period 3. -/
def p1084 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1084 : zipCycle p1084 10 3 false (2) = true := by decide +kernel
theorem never1084 (m : Machine) (hm : compatible p1084 m) : NeverHalts m :=
  zipCycle_sound p1084 10 3 false (2) (by decide) cert1084 m hm
#print axioms never1084


/-- Third-level first-hole refinement 1085, 1RB1RD_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 5, period 4. -/
def p1085 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1085 : zipCycle p1085 5 4 true (0) = true := by decide +kernel
theorem never1085 (m : Machine) (hm : compatible p1085 m) : NeverHalts m :=
  zipCycle_sound p1085 5 4 true (0) (by decide) cert1085 m hm
#print axioms never1085


/-- Third-level first-hole refinement 1086, 1RB0RE_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 9, period 3. -/
def p1086 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1086 : zipCycle p1086 9 3 false (1) = true := by decide +kernel
theorem never1086 (m : Machine) (hm : compatible p1086 m) : NeverHalts m :=
  zipCycle_sound p1086 9 3 false (1) (by decide) cert1086 m hm
#print axioms never1086


/-- Third-level first-hole refinement 1087, 1RB1RE_1RC1LE_0RD---_1LD1RB_---1LA_------; entry 7, period 2. -/
def p1087 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1087 : zipCycle p1087 7 2 true (0) = true := by decide +kernel
theorem never1087 (m : Machine) (hm : compatible p1087 m) : NeverHalts m :=
  zipCycle_sound p1087 7 2 true (0) (by decide) cert1087 m hm
#print axioms never1087


/-- Third-level first-hole refinement 1088, 1RB1LA_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 6, period 4. -/
def p1088 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1088 : zipCycle p1088 6 4 true (1) = true := by decide +kernel
theorem never1088 (m : Machine) (hm : compatible p1088 m) : NeverHalts m :=
  zipCycle_sound p1088 6 4 true (1) (by decide) cert1088 m hm
#print axioms never1088


/-- Third-level first-hole refinement 1089, 1RB0RA_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 0, period 10. -/
def p1089 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1089 : zipCycle p1089 0 10 true (0) = true := by decide +kernel
theorem never1089 (m : Machine) (hm : compatible p1089 m) : NeverHalts m :=
  zipCycle_sound p1089 0 10 true (0) (by decide) cert1089 m hm
#print axioms never1089


/-- Third-level first-hole refinement 1090, 1RB1RA_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 0, period 10. -/
def p1090 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1090 : zipCycle p1090 0 10 true (0) = true := by decide +kernel
theorem never1090 (m : Machine) (hm : compatible p1090 m) : NeverHalts m :=
  zipCycle_sound p1090 0 10 true (0) (by decide) cert1090 m hm
#print axioms never1090


/-- Third-level first-hole refinement 1091, 1RB0LB_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 1, period 11. -/
def p1091 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1091 : zipCycle p1091 1 11 true (1) = true := by decide +kernel
theorem never1091 (m : Machine) (hm : compatible p1091 m) : NeverHalts m :=
  zipCycle_sound p1091 1 11 true (1) (by decide) cert1091 m hm
#print axioms never1091


/-- Third-level first-hole refinement 1092, 1RB1RB_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 1, period 11. -/
def p1092 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1092 : zipCycle p1092 1 11 true (1) = true := by decide +kernel
theorem never1092 (m : Machine) (hm : compatible p1092 m) : NeverHalts m :=
  zipCycle_sound p1092 1 11 true (1) (by decide) cert1092 m hm
#print axioms never1092


/-- Third-level first-hole refinement 1093, 1RB0LC_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 17, period 1. -/
def p1093 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1093 : zipCycle p1093 17 1 false (1) = true := by decide +kernel
theorem never1093 (m : Machine) (hm : compatible p1093 m) : NeverHalts m :=
  zipCycle_sound p1093 17 1 false (1) (by decide) cert1093 m hm
#print axioms never1093


/-- Third-level first-hole refinement 1094, 1RB1LC_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 1, period 15. -/
def p1094 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1094 : zipCycle p1094 1 15 true (1) = true := by decide +kernel
theorem never1094 (m : Machine) (hm : compatible p1094 m) : NeverHalts m :=
  zipCycle_sound p1094 1 15 true (1) (by decide) cert1094 m hm
#print axioms never1094


/-- Third-level first-hole refinement 1095, 1RB0LD_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 14, period 1. -/
def p1095 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1095 : zipCycle p1095 14 1 false (0) = true := by decide +kernel
theorem never1095 (m : Machine) (hm : compatible p1095 m) : NeverHalts m :=
  zipCycle_sound p1095 14 1 false (0) (by decide) cert1095 m hm
#print axioms never1095


/-- Third-level first-hole refinement 1096, 1RB1LD_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 14, period 1. -/
def p1096 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1096 : zipCycle p1096 14 1 false (0) = true := by decide +kernel
theorem never1096 (m : Machine) (hm : compatible p1096 m) : NeverHalts m :=
  zipCycle_sound p1096 14 1 false (0) (by decide) cert1096 m hm
#print axioms never1096


/-- Third-level first-hole refinement 1097, 1RB0RD_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 1, period 9. -/
def p1097 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1097 : zipCycle p1097 1 9 true (1) = true := by decide +kernel
theorem never1097 (m : Machine) (hm : compatible p1097 m) : NeverHalts m :=
  zipCycle_sound p1097 1 9 true (1) (by decide) cert1097 m hm
#print axioms never1097


/-- Third-level first-hole refinement 1098, 1RB1RD_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 1, period 9. -/
def p1098 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1098 : zipCycle p1098 1 9 true (1) = true := by decide +kernel
theorem never1098 (m : Machine) (hm : compatible p1098 m) : NeverHalts m :=
  zipCycle_sound p1098 1 9 true (1) (by decide) cert1098 m hm
#print axioms never1098


/-- Third-level first-hole refinement 1099, 1RB0RE_1RC1LE_0RD---_1LD1RB_---0RA_------; entry 0, period 10. -/
def p1099 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1099 : zipCycle p1099 0 10 true (0) = true := by decide +kernel
theorem never1099 (m : Machine) (hm : compatible p1099 m) : NeverHalts m :=
  zipCycle_sound p1099 0 10 true (0) (by decide) cert1099 m hm
#print axioms never1099

end BB6.Agent24Raw45D3_10
