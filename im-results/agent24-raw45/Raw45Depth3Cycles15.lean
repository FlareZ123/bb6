import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_15
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1500, 1RB---_1RC1RE_0RD0RE_1LD1RB_---1LC_------; entry 1, period 11. -/
def p1500 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1500 : zipCycle p1500 1 11 true (1) = true := by decide +kernel
theorem never1500 (m : Machine) (hm : compatible p1500 m) : NeverHalts m :=
  zipCycle_sound p1500 1 11 true (1) (by decide) cert1500 m hm
#print axioms never1500


/-- Third-level first-hole refinement 1501, 1RB---_1RC1RE_0RD1RE_1LD1RB_---1LC_------; entry 7, period 2. -/
def p1501 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1501 : zipCycle p1501 7 2 true (2) = true := by decide +kernel
theorem never1501 (m : Machine) (hm : compatible p1501 m) : NeverHalts m :=
  zipCycle_sound p1501 7 2 true (2) (by decide) cert1501 m hm
#print axioms never1501


/-- Third-level first-hole refinement 1502, 1RB---_1RC1RE_0RD0LA_1LD1RB_---0RC_------; entry 0, period 16. -/
def p1502 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1502 : zipCycle p1502 0 16 true (0) = true := by decide +kernel
theorem never1502 (m : Machine) (hm : compatible p1502 m) : NeverHalts m :=
  zipCycle_sound p1502 0 16 true (0) (by decide) cert1502 m hm
#print axioms never1502


/-- Third-level first-hole refinement 1503, 1RB---_1RC1RE_0RD0RA_1LD1RB_---0RC_------; entry 0, period 16. -/
def p1503 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1503 : zipCycle p1503 0 16 true (0) = true := by decide +kernel
theorem never1503 (m : Machine) (hm : compatible p1503 m) : NeverHalts m :=
  zipCycle_sound p1503 0 16 true (0) (by decide) cert1503 m hm
#print axioms never1503


/-- Third-level first-hole refinement 1504, 1RB---_1RC1RE_0RD1RA_1LD1RB_---0RC_------; entry 0, period 16. -/
def p1504 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1504 : zipCycle p1504 0 16 true (0) = true := by decide +kernel
theorem never1504 (m : Machine) (hm : compatible p1504 m) : NeverHalts m :=
  zipCycle_sound p1504 0 16 true (0) (by decide) cert1504 m hm
#print axioms never1504


/-- Third-level first-hole refinement 1505, 1RB---_1RC1RE_0RD0LB_1LD1RB_---0RC_------; entry 1, period 15. -/
def p1505 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1505 : zipCycle p1505 1 15 true (1) = true := by decide +kernel
theorem never1505 (m : Machine) (hm : compatible p1505 m) : NeverHalts m :=
  zipCycle_sound p1505 1 15 true (1) (by decide) cert1505 m hm
#print axioms never1505


/-- Third-level first-hole refinement 1506, 1RB---_1RC1RE_0RD1LB_1LD1RB_---0RC_------; entry 6, period 12. -/
def p1506 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1506 : zipCycle p1506 6 12 true (2) = true := by decide +kernel
theorem never1506 (m : Machine) (hm : compatible p1506 m) : NeverHalts m :=
  zipCycle_sound p1506 6 12 true (2) (by decide) cert1506 m hm
#print axioms never1506


/-- Third-level first-hole refinement 1507, 1RB---_1RC1RE_0RD0RB_1LD1RB_---0RC_------; entry 1, period 15. -/
def p1507 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1507 : zipCycle p1507 1 15 true (1) = true := by decide +kernel
theorem never1507 (m : Machine) (hm : compatible p1507 m) : NeverHalts m :=
  zipCycle_sound p1507 1 15 true (1) (by decide) cert1507 m hm
#print axioms never1507


/-- Third-level first-hole refinement 1508, 1RB---_1RC1RE_0RD1RB_1LD1RB_---0RC_------; entry 1, period 15. -/
def p1508 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1508 : zipCycle p1508 1 15 true (1) = true := by decide +kernel
theorem never1508 (m : Machine) (hm : compatible p1508 m) : NeverHalts m :=
  zipCycle_sound p1508 1 15 true (1) (by decide) cert1508 m hm
#print axioms never1508


/-- Third-level first-hole refinement 1509, 1RB---_1RC1RE_0RD0LC_1LD1RB_---0RC_------; entry 2, period 14. -/
def p1509 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1509 : zipCycle p1509 2 14 true (1) = true := by decide +kernel
theorem never1509 (m : Machine) (hm : compatible p1509 m) : NeverHalts m :=
  zipCycle_sound p1509 2 14 true (1) (by decide) cert1509 m hm
#print axioms never1509


/-- Third-level first-hole refinement 1510, 1RB---_1RC1RE_0RD1LC_1LD1RB_---0RC_------; entry 1, period 17. -/
def p1510 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1510 : zipCycle p1510 1 17 true (1) = true := by decide +kernel
theorem never1510 (m : Machine) (hm : compatible p1510 m) : NeverHalts m :=
  zipCycle_sound p1510 1 17 true (1) (by decide) cert1510 m hm
#print axioms never1510


/-- Third-level first-hole refinement 1511, 1RB---_1RC1RE_0RD1RC_1LD1RB_---0RC_------; entry 2, period 14. -/
def p1511 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1511 : zipCycle p1511 2 14 true (1) = true := by decide +kernel
theorem never1511 (m : Machine) (hm : compatible p1511 m) : NeverHalts m :=
  zipCycle_sound p1511 2 14 true (1) (by decide) cert1511 m hm
#print axioms never1511


/-- Third-level first-hole refinement 1512, 1RB---_1RC1RE_0RD1LD_1LD1RB_---0RC_------; entry 4, period 12. -/
def p1512 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1512 : zipCycle p1512 4 12 true (1) = true := by decide +kernel
theorem never1512 (m : Machine) (hm : compatible p1512 m) : NeverHalts m :=
  zipCycle_sound p1512 4 12 true (1) (by decide) cert1512 m hm
#print axioms never1512


/-- Third-level first-hole refinement 1513, 1RB---_1RC1RE_0RD0RD_1LD1RB_---0RC_------; entry 9, period 7. -/
def p1513 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1513 : zipCycle p1513 9 7 true (2) = true := by decide +kernel
theorem never1513 (m : Machine) (hm : compatible p1513 m) : NeverHalts m :=
  zipCycle_sound p1513 9 7 true (2) (by decide) cert1513 m hm
#print axioms never1513


/-- Third-level first-hole refinement 1514, 1RB---_1RC1RE_0RD---_1LD1RB_0RA1LD_------; entry 0, period 11. -/
def p1514 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1514 : zipCycle p1514 0 11 true (0) = true := by decide +kernel
theorem never1514 (m : Machine) (hm : compatible p1514 m) : NeverHalts m :=
  zipCycle_sound p1514 0 11 true (0) (by decide) cert1514 m hm
#print axioms never1514


/-- Third-level first-hole refinement 1515, 1RB---_1RC1RE_0RD---_1LD1RB_1RA1LD_------; entry 0, period 11. -/
def p1515 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1515 : zipCycle p1515 0 11 true (0) = true := by decide +kernel
theorem never1515 (m : Machine) (hm : compatible p1515 m) : NeverHalts m :=
  zipCycle_sound p1515 0 11 true (0) (by decide) cert1515 m hm
#print axioms never1515


/-- Third-level first-hole refinement 1516, 1RB---_1RC1RE_0RD---_1LD1RB_0LB1LD_------; entry 9, period 2. -/
def p1516 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1516 : zipCycle p1516 9 2 true (3) = true := by decide +kernel
theorem never1516 (m : Machine) (hm : compatible p1516 m) : NeverHalts m :=
  zipCycle_sound p1516 9 2 true (3) (by decide) cert1516 m hm
#print axioms never1516


/-- Third-level first-hole refinement 1517, 1RB---_1RC1RE_0RD---_1LD1RB_1LB1LD_------; entry 6, period 5. -/
def p1517 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1517 : zipCycle p1517 6 5 true (2) = true := by decide +kernel
theorem never1517 (m : Machine) (hm : compatible p1517 m) : NeverHalts m :=
  zipCycle_sound p1517 6 5 true (2) (by decide) cert1517 m hm
#print axioms never1517


/-- Third-level first-hole refinement 1518, 1RB---_1RC1RE_0RD---_1LD1RB_0RB1LD_------; entry 1, period 10. -/
def p1518 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1518 : zipCycle p1518 1 10 true (1) = true := by decide +kernel
theorem never1518 (m : Machine) (hm : compatible p1518 m) : NeverHalts m :=
  zipCycle_sound p1518 1 10 true (1) (by decide) cert1518 m hm
#print axioms never1518


/-- Third-level first-hole refinement 1519, 1RB---_1RC1RE_0RD---_1LD1RB_1RB1LD_------; entry 1, period 10. -/
def p1519 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1519 : zipCycle p1519 1 10 true (1) = true := by decide +kernel
theorem never1519 (m : Machine) (hm : compatible p1519 m) : NeverHalts m :=
  zipCycle_sound p1519 1 10 true (1) (by decide) cert1519 m hm
#print axioms never1519


/-- Third-level first-hole refinement 1520, 1RB---_1RC1RE_0RD---_1LD1RB_0RC1LD_------; entry 5, period 13. -/
def p1520 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1520 : zipCycle p1520 5 13 true (1) = true := by decide +kernel
theorem never1520 (m : Machine) (hm : compatible p1520 m) : NeverHalts m :=
  zipCycle_sound p1520 5 13 true (1) (by decide) cert1520 m hm
#print axioms never1520


/-- Third-level first-hole refinement 1521, 1RB---_1RC1RE_0RD---_1LD1RB_1RC1LD_------; entry 2, period 9. -/
def p1521 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1521 : zipCycle p1521 2 9 true (1) = true := by decide +kernel
theorem never1521 (m : Machine) (hm : compatible p1521 m) : NeverHalts m :=
  zipCycle_sound p1521 2 9 true (1) (by decide) cert1521 m hm
#print axioms never1521


/-- Third-level first-hole refinement 1522, 1RB---_1RC1RE_0RD---_1LD1RB_0LD1LD_------; entry 1, period 11. -/
def p1522 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1522 : zipCycle p1522 1 11 true (1) = true := by decide +kernel
theorem never1522 (m : Machine) (hm : compatible p1522 m) : NeverHalts m :=
  zipCycle_sound p1522 1 11 true (1) (by decide) cert1522 m hm
#print axioms never1522


/-- Third-level first-hole refinement 1523, 1RB---_1RC1RE_0RD---_1LD1RB_1LD1LD_------; entry 8, period 3. -/
def p1523 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1523 : zipCycle p1523 8 3 true (2) = true := by decide +kernel
theorem never1523 (m : Machine) (hm : compatible p1523 m) : NeverHalts m :=
  zipCycle_sound p1523 8 3 true (2) (by decide) cert1523 m hm
#print axioms never1523


/-- Third-level first-hole refinement 1524, 1RB---_1RC1RE_0RD---_1LD1RB_0RD1LD_------; entry 3, period 8. -/
def p1524 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1524 : zipCycle p1524 3 8 true (1) = true := by decide +kernel
theorem never1524 (m : Machine) (hm : compatible p1524 m) : NeverHalts m :=
  zipCycle_sound p1524 3 8 true (1) (by decide) cert1524 m hm
#print axioms never1524


/-- Third-level first-hole refinement 1525, 1RB---_1RC1RE_0RD---_1LD1RB_1RD1LD_------; entry 8, period 4. -/
def p1525 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1525 : zipCycle p1525 8 4 true (2) = true := by decide +kernel
theorem never1525 (m : Machine) (hm : compatible p1525 m) : NeverHalts m :=
  zipCycle_sound p1525 8 4 true (2) (by decide) cert1525 m hm
#print axioms never1525


/-- Third-level first-hole refinement 1526, 1RB---_1RC1RE_0RD---_1LD1RB_0LE1LD_------; entry 7, period 4. -/
def p1526 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1526 : zipCycle p1526 7 4 true (2) = true := by decide +kernel
theorem never1526 (m : Machine) (hm : compatible p1526 m) : NeverHalts m :=
  zipCycle_sound p1526 7 4 true (2) (by decide) cert1526 m hm
#print axioms never1526


/-- Third-level first-hole refinement 1527, 1RB---_1RC1RE_0RD---_1LD1RB_1LE1LD_------; entry 5, period 7. -/
def p1527 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1527 : zipCycle p1527 5 7 true (1) = true := by decide +kernel
theorem never1527 (m : Machine) (hm : compatible p1527 m) : NeverHalts m :=
  zipCycle_sound p1527 5 7 true (1) (by decide) cert1527 m hm
#print axioms never1527


/-- Third-level first-hole refinement 1528, 1RB---_1RC1RE_0RD---_1LD1RB_0RE1LD_------; entry 10, period 1. -/
def p1528 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1528 : zipCycle p1528 10 1 true (4) = true := by decide +kernel
theorem never1528 (m : Machine) (hm : compatible p1528 m) : NeverHalts m :=
  zipCycle_sound p1528 10 1 true (4) (by decide) cert1528 m hm
#print axioms never1528


/-- Third-level first-hole refinement 1529, 1RB---_1RC1RE_0RD---_1LD1RB_1RE1LD_------; entry 10, period 1. -/
def p1529 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1529 : zipCycle p1529 10 1 true (4) = true := by decide +kernel
theorem never1529 (m : Machine) (hm : compatible p1529 m) : NeverHalts m :=
  zipCycle_sound p1529 10 1 true (4) (by decide) cert1529 m hm
#print axioms never1529


/-- Third-level first-hole refinement 1530, 1RB---_1RC1RE_0RD---_1LD1RB_0RA1RD_------; entry 0, period 12. -/
def p1530 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1530 : zipCycle p1530 0 12 true (0) = true := by decide +kernel
theorem never1530 (m : Machine) (hm : compatible p1530 m) : NeverHalts m :=
  zipCycle_sound p1530 0 12 true (0) (by decide) cert1530 m hm
#print axioms never1530


/-- Third-level first-hole refinement 1531, 1RB---_1RC1RE_0RD---_1LD1RB_1RA1RD_------; entry 0, period 12. -/
def p1531 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1531 : zipCycle p1531 0 12 true (0) = true := by decide +kernel
theorem never1531 (m : Machine) (hm : compatible p1531 m) : NeverHalts m :=
  zipCycle_sound p1531 0 12 true (0) (by decide) cert1531 m hm
#print axioms never1531


/-- Third-level first-hole refinement 1532, 1RB---_1RC1RE_0RD---_1LD1RB_0LB1RD_------; entry 10, period 2. -/
def p1532 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1532 : zipCycle p1532 10 2 true (4) = true := by decide +kernel
theorem never1532 (m : Machine) (hm : compatible p1532 m) : NeverHalts m :=
  zipCycle_sound p1532 10 2 true (4) (by decide) cert1532 m hm
#print axioms never1532


/-- Third-level first-hole refinement 1533, 1RB---_1RC1RE_0RD---_1LD1RB_1LB1RD_------; entry 6, period 6. -/
def p1533 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1533 : zipCycle p1533 6 6 true (2) = true := by decide +kernel
theorem never1533 (m : Machine) (hm : compatible p1533 m) : NeverHalts m :=
  zipCycle_sound p1533 6 6 true (2) (by decide) cert1533 m hm
#print axioms never1533


/-- Third-level first-hole refinement 1534, 1RB---_1RC1RE_0RD---_1LD1RB_0RB1RD_------; entry 1, period 11. -/
def p1534 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1534 : zipCycle p1534 1 11 true (1) = true := by decide +kernel
theorem never1534 (m : Machine) (hm : compatible p1534 m) : NeverHalts m :=
  zipCycle_sound p1534 1 11 true (1) (by decide) cert1534 m hm
#print axioms never1534


/-- Third-level first-hole refinement 1535, 1RB---_1RC1RE_0RD---_1LD1RB_1RB1RD_------; entry 1, period 11. -/
def p1535 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1535 : zipCycle p1535 1 11 true (1) = true := by decide +kernel
theorem never1535 (m : Machine) (hm : compatible p1535 m) : NeverHalts m :=
  zipCycle_sound p1535 1 11 true (1) (by decide) cert1535 m hm
#print axioms never1535


/-- Third-level first-hole refinement 1536, 1RB---_1RC1RE_0RD---_1LD1RB_0RC1RD_------; entry 1, period 19. -/
def p1536 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1536 : zipCycle p1536 1 19 true (1) = true := by decide +kernel
theorem never1536 (m : Machine) (hm : compatible p1536 m) : NeverHalts m :=
  zipCycle_sound p1536 1 19 true (1) (by decide) cert1536 m hm
#print axioms never1536


/-- Third-level first-hole refinement 1537, 1RB---_1RC1RE_0RD---_1LD1RB_1RC1RD_------; entry 2, period 10. -/
def p1537 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1537 : zipCycle p1537 2 10 true (1) = true := by decide +kernel
theorem never1537 (m : Machine) (hm : compatible p1537 m) : NeverHalts m :=
  zipCycle_sound p1537 2 10 true (1) (by decide) cert1537 m hm
#print axioms never1537


/-- Third-level first-hole refinement 1538, 1RB---_1RC1RE_0RD---_1LD1RB_0LD1RD_------; entry 1, period 12. -/
def p1538 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1538 : zipCycle p1538 1 12 true (1) = true := by decide +kernel
theorem never1538 (m : Machine) (hm : compatible p1538 m) : NeverHalts m :=
  zipCycle_sound p1538 1 12 true (1) (by decide) cert1538 m hm
#print axioms never1538


/-- Third-level first-hole refinement 1539, 1RB---_1RC1RE_0RD---_1LD1RB_1LD1RD_------; entry 9, period 3. -/
def p1539 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1539 : zipCycle p1539 9 3 true (3) = true := by decide +kernel
theorem never1539 (m : Machine) (hm : compatible p1539 m) : NeverHalts m :=
  zipCycle_sound p1539 9 3 true (3) (by decide) cert1539 m hm
#print axioms never1539


/-- Third-level first-hole refinement 1540, 1RB---_1RC1RE_0RD---_1LD1RB_0RD1RD_------; entry 3, period 9. -/
def p1540 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1540 : zipCycle p1540 3 9 true (1) = true := by decide +kernel
theorem never1540 (m : Machine) (hm : compatible p1540 m) : NeverHalts m :=
  zipCycle_sound p1540 3 9 true (1) (by decide) cert1540 m hm
#print axioms never1540


/-- Third-level first-hole refinement 1541, 1RB---_1RC1RE_0RD---_1LD1RB_1RD1RD_------; entry 8, period 4. -/
def p1541 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1541 : zipCycle p1541 8 4 true (3) = true := by decide +kernel
theorem never1541 (m : Machine) (hm : compatible p1541 m) : NeverHalts m :=
  zipCycle_sound p1541 8 4 true (3) (by decide) cert1541 m hm
#print axioms never1541


/-- Third-level first-hole refinement 1542, 1RB---_1RC1RE_0RD---_1LD1RB_0LE1RD_------; entry 7, period 5. -/
def p1542 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1542 : zipCycle p1542 7 5 true (3) = true := by decide +kernel
theorem never1542 (m : Machine) (hm : compatible p1542 m) : NeverHalts m :=
  zipCycle_sound p1542 7 5 true (3) (by decide) cert1542 m hm
#print axioms never1542


/-- Third-level first-hole refinement 1543, 1RB---_1RC1RE_0RD---_1LD1RB_1LE1RD_------; entry 1, period 13. -/
def p1543 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1543 : zipCycle p1543 1 13 true (1) = true := by decide +kernel
theorem never1543 (m : Machine) (hm : compatible p1543 m) : NeverHalts m :=
  zipCycle_sound p1543 1 13 true (1) (by decide) cert1543 m hm
#print axioms never1543


/-- Third-level first-hole refinement 1544, 1RB---_1RC1RE_0RD---_1LD1RB_0RE1RD_------; entry 11, period 1. -/
def p1544 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1544 : zipCycle p1544 11 1 true (5) = true := by decide +kernel
theorem never1544 (m : Machine) (hm : compatible p1544 m) : NeverHalts m :=
  zipCycle_sound p1544 11 1 true (5) (by decide) cert1544 m hm
#print axioms never1544


/-- Third-level first-hole refinement 1545, 1RB---_1RC1RE_0RD---_1LD1RB_1RE1RD_------; entry 11, period 1. -/
def p1545 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1545 : zipCycle p1545 11 1 true (5) = true := by decide +kernel
theorem never1545 (m : Machine) (hm : compatible p1545 m) : NeverHalts m :=
  zipCycle_sound p1545 11 1 true (5) (by decide) cert1545 m hm
#print axioms never1545


/-- Third-level first-hole refinement 1546, 1RB---_1RC1RE_0RD---_1LD1RB_0LA0LE_------; entry 0, period 12. -/
def p1546 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1546 : zipCycle p1546 0 12 false (3) = true := by decide +kernel
theorem never1546 (m : Machine) (hm : compatible p1546 m) : NeverHalts m :=
  zipCycle_sound p1546 0 12 false (3) (by decide) cert1546 m hm
#print axioms never1546


/-- Third-level first-hole refinement 1547, 1RB---_1RC1RE_0RD---_1LD1RB_0RA0LE_------; entry 0, period 12. -/
def p1547 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1547 : zipCycle p1547 0 12 true (-1) = true := by decide +kernel
theorem never1547 (m : Machine) (hm : compatible p1547 m) : NeverHalts m :=
  zipCycle_sound p1547 0 12 true (-1) (by decide) cert1547 m hm
#print axioms never1547


/-- Third-level first-hole refinement 1548, 1RB---_1RC1RE_0RD---_1LD1RB_1RA0LE_------; entry 7, period 13. -/
def p1548 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1548 : zipCycle p1548 7 13 false (3) = true := by decide +kernel
theorem never1548 (m : Machine) (hm : compatible p1548 m) : NeverHalts m :=
  zipCycle_sound p1548 7 13 false (3) (by decide) cert1548 m hm
#print axioms never1548


/-- Third-level first-hole refinement 1549, 1RB---_1RC1RE_0RD---_1LD1RB_0LB0LE_------; entry 8, period 10. -/
def p1549 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1549 : zipCycle p1549 8 10 false (2) = true := by decide +kernel
theorem never1549 (m : Machine) (hm : compatible p1549 m) : NeverHalts m :=
  zipCycle_sound p1549 8 10 false (2) (by decide) cert1549 m hm
#print axioms never1549


/-- Third-level first-hole refinement 1550, 1RB---_1RC1RE_0RD---_1LD1RB_0RB0LE_------; entry 8, period 10. -/
def p1550 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1550 : zipCycle p1550 8 10 true (-1) = true := by decide +kernel
theorem never1550 (m : Machine) (hm : compatible p1550 m) : NeverHalts m :=
  zipCycle_sound p1550 8 10 true (-1) (by decide) cert1550 m hm
#print axioms never1550


/-- Third-level first-hole refinement 1551, 1RB---_1RC1RE_0RD---_1LD1RB_1RB0LE_------; entry 1, period 11. -/
def p1551 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1551 : zipCycle p1551 1 11 false (3) = true := by decide +kernel
theorem never1551 (m : Machine) (hm : compatible p1551 m) : NeverHalts m :=
  zipCycle_sound p1551 1 11 false (3) (by decide) cert1551 m hm
#print axioms never1551


/-- Third-level first-hole refinement 1552, 1RB---_1RC1RE_0RD---_1LD1RB_0LC0LE_------; entry 13, period 1. -/
def p1552 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1552 : zipCycle p1552 13 1 false (-1) = true := by decide +kernel
theorem never1552 (m : Machine) (hm : compatible p1552 m) : NeverHalts m :=
  zipCycle_sound p1552 13 1 false (-1) (by decide) cert1552 m hm
#print axioms never1552


/-- Third-level first-hole refinement 1553, 1RB---_1RC1RE_0RD---_1LD1RB_1LC0LE_------; entry 1, period 13. -/
def p1553 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1553 : zipCycle p1553 1 13 false (3) = true := by decide +kernel
theorem never1553 (m : Machine) (hm : compatible p1553 m) : NeverHalts m :=
  zipCycle_sound p1553 1 13 false (3) (by decide) cert1553 m hm
#print axioms never1553


/-- Third-level first-hole refinement 1554, 1RB---_1RC1RE_0RD---_1LD1RB_0RC0LE_------; entry 13, period 1. -/
def p1554 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1554 : zipCycle p1554 13 1 false (1) = true := by decide +kernel
theorem never1554 (m : Machine) (hm : compatible p1554 m) : NeverHalts m :=
  zipCycle_sound p1554 13 1 false (1) (by decide) cert1554 m hm
#print axioms never1554


/-- Third-level first-hole refinement 1555, 1RB---_1RC1RE_0RD---_1LD1RB_1RC0LE_------; entry 8, period 9. -/
def p1555 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1555 : zipCycle p1555 8 9 false (2) = true := by decide +kernel
theorem never1555 (m : Machine) (hm : compatible p1555 m) : NeverHalts m :=
  zipCycle_sound p1555 8 9 false (2) (by decide) cert1555 m hm
#print axioms never1555


/-- Third-level first-hole refinement 1556, 1RB---_1RC1RE_0RD---_1LD1RB_0LD0LE_------; entry 12, period 1. -/
def p1556 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1556 : zipCycle p1556 12 1 false (-2) = true := by decide +kernel
theorem never1556 (m : Machine) (hm : compatible p1556 m) : NeverHalts m :=
  zipCycle_sound p1556 12 1 false (-2) (by decide) cert1556 m hm
#print axioms never1556


/-- Third-level first-hole refinement 1557, 1RB---_1RC1RE_0RD---_1LD1RB_1LD0LE_------; entry 12, period 1. -/
def p1557 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1557 : zipCycle p1557 12 1 false (-2) = true := by decide +kernel
theorem never1557 (m : Machine) (hm : compatible p1557 m) : NeverHalts m :=
  zipCycle_sound p1557 12 1 false (-2) (by decide) cert1557 m hm
#print axioms never1557


/-- Third-level first-hole refinement 1558, 1RB---_1RC1RE_0RD---_1LD1RB_0RD0LE_------; entry 12, period 1. -/
def p1558 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1558 : zipCycle p1558 12 1 false (0) = true := by decide +kernel
theorem never1558 (m : Machine) (hm : compatible p1558 m) : NeverHalts m :=
  zipCycle_sound p1558 12 1 false (0) (by decide) cert1558 m hm
#print axioms never1558


/-- Third-level first-hole refinement 1559, 1RB---_1RC1RE_0RD---_1LD1RB_1RD0LE_------; entry 11, period 4. -/
def p1559 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1559 : zipCycle p1559 11 4 true (-1) = true := by decide +kernel
theorem never1559 (m : Machine) (hm : compatible p1559 m) : NeverHalts m :=
  zipCycle_sound p1559 11 4 true (-1) (by decide) cert1559 m hm
#print axioms never1559


/-- Third-level first-hole refinement 1560, 1RB---_1RC1RE_0RD---_1LD1RB_0LE0LE_------; entry 11, period 1. -/
def p1560 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1560 : zipCycle p1560 11 1 false (-1) = true := by decide +kernel
theorem never1560 (m : Machine) (hm : compatible p1560 m) : NeverHalts m :=
  zipCycle_sound p1560 11 1 false (-1) (by decide) cert1560 m hm
#print axioms never1560


/-- Third-level first-hole refinement 1561, 1RB---_1RC1RE_0RD---_1LD1RB_1LE0LE_------; entry 11, period 1. -/
def p1561 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1561 : zipCycle p1561 11 1 false (-1) = true := by decide +kernel
theorem never1561 (m : Machine) (hm : compatible p1561 m) : NeverHalts m :=
  zipCycle_sound p1561 11 1 false (-1) (by decide) cert1561 m hm
#print axioms never1561


/-- Third-level first-hole refinement 1562, 1RB---_1RC1RE_0RD---_1LD1RB_0RE0LE_------; entry 11, period 1. -/
def p1562 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1562 : zipCycle p1562 11 1 true (-1) = true := by decide +kernel
theorem never1562 (m : Machine) (hm : compatible p1562 m) : NeverHalts m :=
  zipCycle_sound p1562 11 1 true (-1) (by decide) cert1562 m hm
#print axioms never1562


/-- Third-level first-hole refinement 1563, 1RB---_1RC1RE_0RD---_1LD1RB_1RE0LE_------; entry 11, period 1. -/
def p1563 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1563 : zipCycle p1563 11 1 true (-1) = true := by decide +kernel
theorem never1563 (m : Machine) (hm : compatible p1563 m) : NeverHalts m :=
  zipCycle_sound p1563 11 1 true (-1) (by decide) cert1563 m hm
#print axioms never1563


/-- Third-level first-hole refinement 1564, 1RB---_1RC1RE_0RD---_1LD1RB_1LA1LE_------; entry 8, period 6. -/
def p1564 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1564 : zipCycle p1564 8 6 false (2) = true := by decide +kernel
theorem never1564 (m : Machine) (hm : compatible p1564 m) : NeverHalts m :=
  zipCycle_sound p1564 8 6 false (2) (by decide) cert1564 m hm
#print axioms never1564


/-- Third-level first-hole refinement 1565, 1RB---_1RC1RE_0RD---_1LD1RB_0LB1LE_------; entry 19, period 2. -/
def p1565 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1565 : zipCycle p1565 19 2 true (-2) = true := by decide +kernel
theorem never1565 (m : Machine) (hm : compatible p1565 m) : NeverHalts m :=
  zipCycle_sound p1565 19 2 true (-2) (by decide) cert1565 m hm
#print axioms never1565


/-- Third-level first-hole refinement 1566, 1RB---_1RC1RE_0RD---_1LD1RB_0RB1LE_------; entry 9, period 4. -/
def p1566 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1566 : zipCycle p1566 9 4 true (-1) = true := by decide +kernel
theorem never1566 (m : Machine) (hm : compatible p1566 m) : NeverHalts m :=
  zipCycle_sound p1566 9 4 true (-1) (by decide) cert1566 m hm
#print axioms never1566


/-- Third-level first-hole refinement 1567, 1RB---_1RC1RE_0RD---_1LD1RB_1RB1LE_------; entry 8, period 5. -/
def p1567 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1567 : zipCycle p1567 8 5 false (2) = true := by decide +kernel
theorem never1567 (m : Machine) (hm : compatible p1567 m) : NeverHalts m :=
  zipCycle_sound p1567 8 5 false (2) (by decide) cert1567 m hm
#print axioms never1567


/-- Third-level first-hole refinement 1568, 1RB---_1RC1RE_0RD---_1LD1RB_0LC1LE_------; entry 13, period 1. -/
def p1568 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1568 : zipCycle p1568 13 1 false (-1) = true := by decide +kernel
theorem never1568 (m : Machine) (hm : compatible p1568 m) : NeverHalts m :=
  zipCycle_sound p1568 13 1 false (-1) (by decide) cert1568 m hm
#print axioms never1568


/-- Third-level first-hole refinement 1569, 1RB---_1RC1RE_0RD---_1LD1RB_1LC1LE_------; entry 8, period 7. -/
def p1569 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1569 : zipCycle p1569 8 7 false (2) = true := by decide +kernel
theorem never1569 (m : Machine) (hm : compatible p1569 m) : NeverHalts m :=
  zipCycle_sound p1569 8 7 false (2) (by decide) cert1569 m hm
#print axioms never1569


/-- Third-level first-hole refinement 1570, 1RB---_1RC1RE_0RD---_1LD1RB_0LD1LE_------; entry 12, period 1. -/
def p1570 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1570 : zipCycle p1570 12 1 false (-2) = true := by decide +kernel
theorem never1570 (m : Machine) (hm : compatible p1570 m) : NeverHalts m :=
  zipCycle_sound p1570 12 1 false (-2) (by decide) cert1570 m hm
#print axioms never1570


/-- Third-level first-hole refinement 1571, 1RB---_1RC1RE_0RD---_1LD1RB_1LD1LE_------; entry 12, period 1. -/
def p1571 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1571 : zipCycle p1571 12 1 false (-2) = true := by decide +kernel
theorem never1571 (m : Machine) (hm : compatible p1571 m) : NeverHalts m :=
  zipCycle_sound p1571 12 1 false (-2) (by decide) cert1571 m hm
#print axioms never1571


/-- Third-level first-hole refinement 1572, 1RB---_1RC1RE_0RD---_1LD1RB_0RD1LE_------; entry 8, period 6. -/
def p1572 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1572 : zipCycle p1572 8 6 true (-1) = true := by decide +kernel
theorem never1572 (m : Machine) (hm : compatible p1572 m) : NeverHalts m :=
  zipCycle_sound p1572 8 6 true (-1) (by decide) cert1572 m hm
#print axioms never1572


/-- Third-level first-hole refinement 1573, 1RB---_1RC1RE_0RD---_1LD1RB_1RD1LE_------; entry 5, period 7. -/
def p1573 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1573 : zipCycle p1573 5 7 false (3) = true := by decide +kernel
theorem never1573 (m : Machine) (hm : compatible p1573 m) : NeverHalts m :=
  zipCycle_sound p1573 5 7 false (3) (by decide) cert1573 m hm
#print axioms never1573


/-- Third-level first-hole refinement 1574, 1RB---_1RC1RE_0RD---_1LD1RB_0LE1LE_------; entry 11, period 1. -/
def p1574 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1574 : zipCycle p1574 11 1 false (-1) = true := by decide +kernel
theorem never1574 (m : Machine) (hm : compatible p1574 m) : NeverHalts m :=
  zipCycle_sound p1574 11 1 false (-1) (by decide) cert1574 m hm
#print axioms never1574


/-- Third-level first-hole refinement 1575, 1RB---_1RC1RE_0RD---_1LD1RB_1LE1LE_------; entry 11, period 1. -/
def p1575 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1575 : zipCycle p1575 11 1 false (-1) = true := by decide +kernel
theorem never1575 (m : Machine) (hm : compatible p1575 m) : NeverHalts m :=
  zipCycle_sound p1575 11 1 false (-1) (by decide) cert1575 m hm
#print axioms never1575


/-- Third-level first-hole refinement 1576, 1RB---_1RC1RE_0RD---_1LD1RB_0RE1LE_------; entry 10, period 2. -/
def p1576 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1576 : zipCycle p1576 10 2 true (-1) = true := by decide +kernel
theorem never1576 (m : Machine) (hm : compatible p1576 m) : NeverHalts m :=
  zipCycle_sound p1576 10 2 true (-1) (by decide) cert1576 m hm
#print axioms never1576


/-- Third-level first-hole refinement 1577, 1RB---_1RC1RE_0RD---_1LD1RB_1RE1LE_------; entry 9, period 3. -/
def p1577 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1577 : zipCycle p1577 9 3 false (1) = true := by decide +kernel
theorem never1577 (m : Machine) (hm : compatible p1577 m) : NeverHalts m :=
  zipCycle_sound p1577 9 3 false (1) (by decide) cert1577 m hm
#print axioms never1577


/-- Third-level first-hole refinement 1578, 1RB---_1RC1RE_0RD---_1LD1RB_0LA0RE_------; entry 0, period 9. -/
def p1578 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1578 : zipCycle p1578 0 9 true (0) = true := by decide +kernel
theorem never1578 (m : Machine) (hm : compatible p1578 m) : NeverHalts m :=
  zipCycle_sound p1578 0 9 true (0) (by decide) cert1578 m hm
#print axioms never1578


/-- Third-level first-hole refinement 1579, 1RB---_1RC1RE_0RD---_1LD1RB_0RA0RE_------; entry 0, period 9. -/
def p1579 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1579 : zipCycle p1579 0 9 true (0) = true := by decide +kernel
theorem never1579 (m : Machine) (hm : compatible p1579 m) : NeverHalts m :=
  zipCycle_sound p1579 0 9 true (0) (by decide) cert1579 m hm
#print axioms never1579


/-- Third-level first-hole refinement 1580, 1RB---_1RC1RE_0RD---_1LD1RB_1RA0RE_------; entry 0, period 9. -/
def p1580 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1580 : zipCycle p1580 0 9 true (0) = true := by decide +kernel
theorem never1580 (m : Machine) (hm : compatible p1580 m) : NeverHalts m :=
  zipCycle_sound p1580 0 9 true (0) (by decide) cert1580 m hm
#print axioms never1580


/-- Third-level first-hole refinement 1581, 1RB---_1RC1RE_0RD---_1LD1RB_0LB0RE_------; entry 1, period 8. -/
def p1581 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1581 : zipCycle p1581 1 8 true (1) = true := by decide +kernel
theorem never1581 (m : Machine) (hm : compatible p1581 m) : NeverHalts m :=
  zipCycle_sound p1581 1 8 true (1) (by decide) cert1581 m hm
#print axioms never1581


/-- Third-level first-hole refinement 1582, 1RB---_1RC1RE_0RD---_1LD1RB_0RB0RE_------; entry 1, period 8. -/
def p1582 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1582 : zipCycle p1582 1 8 true (1) = true := by decide +kernel
theorem never1582 (m : Machine) (hm : compatible p1582 m) : NeverHalts m :=
  zipCycle_sound p1582 1 8 true (1) (by decide) cert1582 m hm
#print axioms never1582


/-- Third-level first-hole refinement 1583, 1RB---_1RC1RE_0RD---_1LD1RB_1RB0RE_------; entry 1, period 8. -/
def p1583 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1583 : zipCycle p1583 1 8 true (1) = true := by decide +kernel
theorem never1583 (m : Machine) (hm : compatible p1583 m) : NeverHalts m :=
  zipCycle_sound p1583 1 8 true (1) (by decide) cert1583 m hm
#print axioms never1583


/-- Third-level first-hole refinement 1584, 1RB---_1RC1RE_0RD---_1LD1RB_0LC0RE_------; entry 2, period 7. -/
def p1584 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1584 : zipCycle p1584 2 7 true (1) = true := by decide +kernel
theorem never1584 (m : Machine) (hm : compatible p1584 m) : NeverHalts m :=
  zipCycle_sound p1584 2 7 true (1) (by decide) cert1584 m hm
#print axioms never1584


/-- Third-level first-hole refinement 1585, 1RB---_1RC1RE_0RD---_1LD1RB_1LC0RE_------; entry 1, period 10. -/
def p1585 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1585 : zipCycle p1585 1 10 true (1) = true := by decide +kernel
theorem never1585 (m : Machine) (hm : compatible p1585 m) : NeverHalts m :=
  zipCycle_sound p1585 1 10 true (1) (by decide) cert1585 m hm
#print axioms never1585


/-- Third-level first-hole refinement 1586, 1RB---_1RC1RE_0RD---_1LD1RB_1RC0RE_------; entry 2, period 7. -/
def p1586 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1586 : zipCycle p1586 2 7 true (1) = true := by decide +kernel
theorem never1586 (m : Machine) (hm : compatible p1586 m) : NeverHalts m :=
  zipCycle_sound p1586 2 7 true (1) (by decide) cert1586 m hm
#print axioms never1586


/-- Third-level first-hole refinement 1587, 1RB---_1RC1RE_0RD---_1LD1RB_0LD0RE_------; entry 1, period 13. -/
def p1587 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1587 : zipCycle p1587 1 13 true (1) = true := by decide +kernel
theorem never1587 (m : Machine) (hm : compatible p1587 m) : NeverHalts m :=
  zipCycle_sound p1587 1 13 true (1) (by decide) cert1587 m hm
#print axioms never1587


/-- Third-level first-hole refinement 1588, 1RB---_1RC1RE_0RD---_1LD1RB_1LD0RE_------; entry 4, period 5. -/
def p1588 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1588 : zipCycle p1588 4 5 true (1) = true := by decide +kernel
theorem never1588 (m : Machine) (hm : compatible p1588 m) : NeverHalts m :=
  zipCycle_sound p1588 4 5 true (1) (by decide) cert1588 m hm
#print axioms never1588


/-- Third-level first-hole refinement 1589, 1RB---_1RC1RE_0RD---_1LD1RB_1RD0RE_------; entry 8, period 4. -/
def p1589 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1589 : zipCycle p1589 8 4 true (4) = true := by decide +kernel
theorem never1589 (m : Machine) (hm : compatible p1589 m) : NeverHalts m :=
  zipCycle_sound p1589 8 4 true (4) (by decide) cert1589 m hm
#print axioms never1589


/-- Third-level first-hole refinement 1590, 1RB---_1RC1RE_0RD---_1LD1RB_0LE0RE_------; entry 17, period 1. -/
def p1590 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1590 : zipCycle p1590 17 1 false (1) = true := by decide +kernel
theorem never1590 (m : Machine) (hm : compatible p1590 m) : NeverHalts m :=
  zipCycle_sound p1590 17 1 false (1) (by decide) cert1590 m hm
#print axioms never1590


/-- Third-level first-hole refinement 1591, 1RB---_1RC1RE_0RD---_1LD1RB_1LE0RE_------; entry 35, period 1. -/
def p1591 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1591 : zipCycle p1591 35 1 false (7) = true := by decide +kernel
theorem never1591 (m : Machine) (hm : compatible p1591 m) : NeverHalts m :=
  zipCycle_sound p1591 35 1 false (7) (by decide) cert1591 m hm
#print axioms never1591


/-- Third-level first-hole refinement 1592, 1RB---_1RC1RE_0RD---_1LD1RB_0RE0RE_------; entry 8, period 1. -/
def p1592 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1592 : zipCycle p1592 8 1 true (4) = true := by decide +kernel
theorem never1592 (m : Machine) (hm : compatible p1592 m) : NeverHalts m :=
  zipCycle_sound p1592 8 1 true (4) (by decide) cert1592 m hm
#print axioms never1592


/-- Third-level first-hole refinement 1593, 1RB---_1RC1RE_0RD---_1LD1RB_1RE0RE_------; entry 8, period 1. -/
def p1593 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1593 : zipCycle p1593 8 1 true (4) = true := by decide +kernel
theorem never1593 (m : Machine) (hm : compatible p1593 m) : NeverHalts m :=
  zipCycle_sound p1593 8 1 true (4) (by decide) cert1593 m hm
#print axioms never1593


/-- Third-level first-hole refinement 1594, 1RB---_1RC1RE_0RD---_1LD1RB_0RA1RE_------; entry 0, period 9. -/
def p1594 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1594 : zipCycle p1594 0 9 true (0) = true := by decide +kernel
theorem never1594 (m : Machine) (hm : compatible p1594 m) : NeverHalts m :=
  zipCycle_sound p1594 0 9 true (0) (by decide) cert1594 m hm
#print axioms never1594


/-- Third-level first-hole refinement 1595, 1RB---_1RC1RE_0RD---_1LD1RB_1RA1RE_------; entry 0, period 9. -/
def p1595 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1595 : zipCycle p1595 0 9 true (0) = true := by decide +kernel
theorem never1595 (m : Machine) (hm : compatible p1595 m) : NeverHalts m :=
  zipCycle_sound p1595 0 9 true (0) (by decide) cert1595 m hm
#print axioms never1595


/-- Third-level first-hole refinement 1596, 1RB---_1RC1RE_0RD---_1LD1RB_0LB1RE_------; entry 8, period 2. -/
def p1596 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1596 : zipCycle p1596 8 2 true (3) = true := by decide +kernel
theorem never1596 (m : Machine) (hm : compatible p1596 m) : NeverHalts m :=
  zipCycle_sound p1596 8 2 true (3) (by decide) cert1596 m hm
#print axioms never1596


/-- Third-level first-hole refinement 1597, 1RB---_1RC1RE_0RD---_1LD1RB_1LB1RE_------; entry 6, period 3. -/
def p1597 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1597 : zipCycle p1597 6 3 true (2) = true := by decide +kernel
theorem never1597 (m : Machine) (hm : compatible p1597 m) : NeverHalts m :=
  zipCycle_sound p1597 6 3 true (2) (by decide) cert1597 m hm
#print axioms never1597


/-- Third-level first-hole refinement 1598, 1RB---_1RC1RE_0RD---_1LD1RB_0RB1RE_------; entry 1, period 8. -/
def p1598 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1598 : zipCycle p1598 1 8 true (1) = true := by decide +kernel
theorem never1598 (m : Machine) (hm : compatible p1598 m) : NeverHalts m :=
  zipCycle_sound p1598 1 8 true (1) (by decide) cert1598 m hm
#print axioms never1598


/-- Third-level first-hole refinement 1599, 1RB---_1RC1RE_0RD---_1LD1RB_1RB1RE_------; entry 1, period 8. -/
def p1599 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1599 : zipCycle p1599 1 8 true (1) = true := by decide +kernel
theorem never1599 (m : Machine) (hm : compatible p1599 m) : NeverHalts m :=
  zipCycle_sound p1599 1 8 true (1) (by decide) cert1599 m hm
#print axioms never1599

end BB6.Agent24Raw45D3_15
