import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_16
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1600, 1RB---_1RC1RE_0RD---_1LD1RB_0RC1RE_------; entry 7, period 9. -/
def p1600 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1600 : zipCycle p1600 7 9 true (3) = true := by decide +kernel
theorem never1600 (m : Machine) (hm : compatible p1600 m) : NeverHalts m :=
  zipCycle_sound p1600 7 9 true (3) (by decide) cert1600 m hm
#print axioms never1600


/-- Third-level first-hole refinement 1601, 1RB---_1RC1RE_0RD---_1LD1RB_1RC1RE_------; entry 2, period 7. -/
def p1601 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1601 : zipCycle p1601 2 7 true (1) = true := by decide +kernel
theorem never1601 (m : Machine) (hm : compatible p1601 m) : NeverHalts m :=
  zipCycle_sound p1601 2 7 true (1) (by decide) cert1601 m hm
#print axioms never1601


/-- Third-level first-hole refinement 1602, 1RB---_1RC1RE_0RD---_1LD1RB_0LD1RE_------; entry 1, period 9. -/
def p1602 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1602 : zipCycle p1602 1 9 true (1) = true := by decide +kernel
theorem never1602 (m : Machine) (hm : compatible p1602 m) : NeverHalts m :=
  zipCycle_sound p1602 1 9 true (1) (by decide) cert1602 m hm
#print axioms never1602


/-- Third-level first-hole refinement 1603, 1RB---_1RC1RE_0RD---_1LD1RB_1LD1RE_------; entry 8, period 3. -/
def p1603 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1603 : zipCycle p1603 8 3 true (3) = true := by decide +kernel
theorem never1603 (m : Machine) (hm : compatible p1603 m) : NeverHalts m :=
  zipCycle_sound p1603 8 3 true (3) (by decide) cert1603 m hm
#print axioms never1603


/-- Third-level first-hole refinement 1604, 1RB---_1RC1RE_0RD---_1LD1RB_0RD1RE_------; entry 3, period 6. -/
def p1604 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1604 : zipCycle p1604 3 6 true (1) = true := by decide +kernel
theorem never1604 (m : Machine) (hm : compatible p1604 m) : NeverHalts m :=
  zipCycle_sound p1604 3 6 true (1) (by decide) cert1604 m hm
#print axioms never1604


/-- Third-level first-hole refinement 1605, 1RB---_1RC1RE_0RD---_1LD1RB_1RD1RE_------; entry 8, period 4. -/
def p1605 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1605 : zipCycle p1605 8 4 true (4) = true := by decide +kernel
theorem never1605 (m : Machine) (hm : compatible p1605 m) : NeverHalts m :=
  zipCycle_sound p1605 8 4 true (4) (by decide) cert1605 m hm
#print axioms never1605


/-- Third-level first-hole refinement 1606, 1RB---_1RC1RE_0RD---_1LD1RB_0LE1RE_------; entry 7, period 2. -/
def p1606 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1606 : zipCycle p1606 7 2 true (3) = true := by decide +kernel
theorem never1606 (m : Machine) (hm : compatible p1606 m) : NeverHalts m :=
  zipCycle_sound p1606 7 2 true (3) (by decide) cert1606 m hm
#print axioms never1606


/-- Third-level first-hole refinement 1607, 1RB---_1RC1RE_0RD---_1LD1RB_1LE1RE_------; entry 7, period 3. -/
def p1607 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1607 : zipCycle p1607 7 3 true (3) = true := by decide +kernel
theorem never1607 (m : Machine) (hm : compatible p1607 m) : NeverHalts m :=
  zipCycle_sound p1607 7 3 true (3) (by decide) cert1607 m hm
#print axioms never1607


/-- Third-level first-hole refinement 1608, 1RB---_1RC1RE_0RD---_1LD1RB_0RE1RE_------; entry 8, period 1. -/
def p1608 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1608 : zipCycle p1608 8 1 true (4) = true := by decide +kernel
theorem never1608 (m : Machine) (hm : compatible p1608 m) : NeverHalts m :=
  zipCycle_sound p1608 8 1 true (4) (by decide) cert1608 m hm
#print axioms never1608


/-- Third-level first-hole refinement 1609, 1RB---_1RC1RE_0RD---_1LD1RB_1RE1RE_------; entry 8, period 1. -/
def p1609 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1609 : zipCycle p1609 8 1 true (4) = true := by decide +kernel
theorem never1609 (m : Machine) (hm : compatible p1609 m) : NeverHalts m :=
  zipCycle_sound p1609 8 1 true (4) (by decide) cert1609 m hm
#print axioms never1609


/-- Third-level first-hole refinement 1610, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---0RA; entry 0, period 9. -/
def p1610 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1610 : zipCycle p1610 0 9 true (0) = true := by decide +kernel
theorem never1610 (m : Machine) (hm : compatible p1610 m) : NeverHalts m :=
  zipCycle_sound p1610 0 9 true (0) (by decide) cert1610 m hm
#print axioms never1610


/-- Third-level first-hole refinement 1611, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---1RA; entry 0, period 9. -/
def p1611 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1611 : zipCycle p1611 0 9 true (0) = true := by decide +kernel
theorem never1611 (m : Machine) (hm : compatible p1611 m) : NeverHalts m :=
  zipCycle_sound p1611 0 9 true (0) (by decide) cert1611 m hm
#print axioms never1611


/-- Third-level first-hole refinement 1612, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---0RB; entry 1, period 8. -/
def p1612 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1612 : zipCycle p1612 1 8 true (1) = true := by decide +kernel
theorem never1612 (m : Machine) (hm : compatible p1612 m) : NeverHalts m :=
  zipCycle_sound p1612 1 8 true (1) (by decide) cert1612 m hm
#print axioms never1612


/-- Third-level first-hole refinement 1613, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---1RB; entry 1, period 8. -/
def p1613 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1613 : zipCycle p1613 1 8 true (1) = true := by decide +kernel
theorem never1613 (m : Machine) (hm : compatible p1613 m) : NeverHalts m :=
  zipCycle_sound p1613 1 8 true (1) (by decide) cert1613 m hm
#print axioms never1613


/-- Third-level first-hole refinement 1614, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---0RC; entry 1, period 18. -/
def p1614 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1614 : zipCycle p1614 1 18 true (1) = true := by decide +kernel
theorem never1614 (m : Machine) (hm : compatible p1614 m) : NeverHalts m :=
  zipCycle_sound p1614 1 18 true (1) (by decide) cert1614 m hm
#print axioms never1614


/-- Third-level first-hole refinement 1615, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---1RC; entry 2, period 7. -/
def p1615 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1615 : zipCycle p1615 2 7 true (1) = true := by decide +kernel
theorem never1615 (m : Machine) (hm : compatible p1615 m) : NeverHalts m :=
  zipCycle_sound p1615 2 7 true (1) (by decide) cert1615 m hm
#print axioms never1615


/-- Third-level first-hole refinement 1616, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---0LD; entry 1, period 9. -/
def p1616 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1616 : zipCycle p1616 1 9 true (1) = true := by decide +kernel
theorem never1616 (m : Machine) (hm : compatible p1616 m) : NeverHalts m :=
  zipCycle_sound p1616 1 9 true (1) (by decide) cert1616 m hm
#print axioms never1616


/-- Third-level first-hole refinement 1617, 1RB---_1RC1RE_0RD---_1LD1RB_---0LF_---0RD; entry 3, period 6. -/
def p1617 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1617 : zipCycle p1617 3 6 true (1) = true := by decide +kernel
theorem never1617 (m : Machine) (hm : compatible p1617 m) : NeverHalts m :=
  zipCycle_sound p1617 3 6 true (1) (by decide) cert1617 m hm
#print axioms never1617


/-- Third-level first-hole refinement 1618, 1RB---_1RC1RE_0RD---_1LD1RB_---1LF_---1LD; entry 5, period 4. -/
def p1618 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1618 : zipCycle p1618 5 4 true (1) = true := by decide +kernel
theorem never1618 (m : Machine) (hm : compatible p1618 m) : NeverHalts m :=
  zipCycle_sound p1618 5 4 true (1) (by decide) cert1618 m hm
#print axioms never1618


/-- Third-level first-hole refinement 1619, 1RB---_1RC1RE_0RD---_1LD1RB_---1LF_---0RD; entry 1, period 9. -/
def p1619 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1619 : zipCycle p1619 1 9 true (1) = true := by decide +kernel
theorem never1619 (m : Machine) (hm : compatible p1619 m) : NeverHalts m :=
  zipCycle_sound p1619 1 9 true (1) (by decide) cert1619 m hm
#print axioms never1619


/-- Third-level first-hole refinement 1620, 1RB---_1RC1RE_0RD---_1LD1RB_---1LF_---1RD; entry 1, period 9. -/
def p1620 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1620 : zipCycle p1620 1 9 true (1) = true := by decide +kernel
theorem never1620 (m : Machine) (hm : compatible p1620 m) : NeverHalts m :=
  zipCycle_sound p1620 1 9 true (1) (by decide) cert1620 m hm
#print axioms never1620


/-- Third-level first-hole refinement 1621, 1RB---_1RC1RE_0RD---_1LD1RB_---1LF_---1RE; entry 7, period 2. -/
def p1621 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1621 : zipCycle p1621 7 2 true (2) = true := by decide +kernel
theorem never1621 (m : Machine) (hm : compatible p1621 m) : NeverHalts m :=
  zipCycle_sound p1621 7 2 true (2) (by decide) cert1621 m hm
#print axioms never1621


/-- Third-level first-hole refinement 1622, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_0LA---; entry 0, period 9. -/
def p1622 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1622 : zipCycle p1622 0 9 true (0) = true := by decide +kernel
theorem never1622 (m : Machine) (hm : compatible p1622 m) : NeverHalts m :=
  zipCycle_sound p1622 0 9 true (0) (by decide) cert1622 m hm
#print axioms never1622


/-- Third-level first-hole refinement 1623, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_0RA---; entry 0, period 9. -/
def p1623 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1623 : zipCycle p1623 0 9 true (0) = true := by decide +kernel
theorem never1623 (m : Machine) (hm : compatible p1623 m) : NeverHalts m :=
  zipCycle_sound p1623 0 9 true (0) (by decide) cert1623 m hm
#print axioms never1623


/-- Third-level first-hole refinement 1624, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_1RA---; entry 0, period 9. -/
def p1624 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1624 : zipCycle p1624 0 9 true (0) = true := by decide +kernel
theorem never1624 (m : Machine) (hm : compatible p1624 m) : NeverHalts m :=
  zipCycle_sound p1624 0 9 true (0) (by decide) cert1624 m hm
#print axioms never1624


/-- Third-level first-hole refinement 1625, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_0LB---; entry 1, period 8. -/
def p1625 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1625 : zipCycle p1625 1 8 true (1) = true := by decide +kernel
theorem never1625 (m : Machine) (hm : compatible p1625 m) : NeverHalts m :=
  zipCycle_sound p1625 1 8 true (1) (by decide) cert1625 m hm
#print axioms never1625


/-- Third-level first-hole refinement 1626, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_0RB---; entry 1, period 8. -/
def p1626 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1626 : zipCycle p1626 1 8 true (1) = true := by decide +kernel
theorem never1626 (m : Machine) (hm : compatible p1626 m) : NeverHalts m :=
  zipCycle_sound p1626 1 8 true (1) (by decide) cert1626 m hm
#print axioms never1626


/-- Third-level first-hole refinement 1627, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_1RB---; entry 1, period 8. -/
def p1627 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1627 : zipCycle p1627 1 8 true (1) = true := by decide +kernel
theorem never1627 (m : Machine) (hm : compatible p1627 m) : NeverHalts m :=
  zipCycle_sound p1627 1 8 true (1) (by decide) cert1627 m hm
#print axioms never1627


/-- Third-level first-hole refinement 1628, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_0LC---; entry 2, period 7. -/
def p1628 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1628 : zipCycle p1628 2 7 true (1) = true := by decide +kernel
theorem never1628 (m : Machine) (hm : compatible p1628 m) : NeverHalts m :=
  zipCycle_sound p1628 2 7 true (1) (by decide) cert1628 m hm
#print axioms never1628


/-- Third-level first-hole refinement 1629, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_1LC---; entry 1, period 10. -/
def p1629 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1629 : zipCycle p1629 1 10 true (1) = true := by decide +kernel
theorem never1629 (m : Machine) (hm : compatible p1629 m) : NeverHalts m :=
  zipCycle_sound p1629 1 10 true (1) (by decide) cert1629 m hm
#print axioms never1629


/-- Third-level first-hole refinement 1630, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_1RC---; entry 2, period 7. -/
def p1630 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1630 : zipCycle p1630 2 7 true (1) = true := by decide +kernel
theorem never1630 (m : Machine) (hm : compatible p1630 m) : NeverHalts m :=
  zipCycle_sound p1630 2 7 true (1) (by decide) cert1630 m hm
#print axioms never1630


/-- Third-level first-hole refinement 1631, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_1LD---; entry 4, period 5. -/
def p1631 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1631 : zipCycle p1631 4 5 true (1) = true := by decide +kernel
theorem never1631 (m : Machine) (hm : compatible p1631 m) : NeverHalts m :=
  zipCycle_sound p1631 4 5 true (1) (by decide) cert1631 m hm
#print axioms never1631


/-- Third-level first-hole refinement 1632, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_0RF---; entry 8, period 1. -/
def p1632 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,5⟩)
  | _,_ => none
theorem cert1632 : zipCycle p1632 8 1 true (4) = true := by decide +kernel
theorem never1632 (m : Machine) (hm : compatible p1632 m) : NeverHalts m :=
  zipCycle_sound p1632 8 1 true (4) (by decide) cert1632 m hm
#print axioms never1632


/-- Third-level first-hole refinement 1633, 1RB---_1RC1RE_0RD---_1LD1RB_---0RF_1RF---; entry 8, period 1. -/
def p1633 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,5⟩)
  | _,_ => none
theorem cert1633 : zipCycle p1633 8 1 true (4) = true := by decide +kernel
theorem never1633 (m : Machine) (hm : compatible p1633 m) : NeverHalts m :=
  zipCycle_sound p1633 8 1 true (4) (by decide) cert1633 m hm
#print axioms never1633


/-- Third-level first-hole refinement 1634, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_0RA---; entry 0, period 9. -/
def p1634 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1634 : zipCycle p1634 0 9 true (0) = true := by decide +kernel
theorem never1634 (m : Machine) (hm : compatible p1634 m) : NeverHalts m :=
  zipCycle_sound p1634 0 9 true (0) (by decide) cert1634 m hm
#print axioms never1634


/-- Third-level first-hole refinement 1635, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_1RA---; entry 0, period 9. -/
def p1635 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1635 : zipCycle p1635 0 9 true (0) = true := by decide +kernel
theorem never1635 (m : Machine) (hm : compatible p1635 m) : NeverHalts m :=
  zipCycle_sound p1635 0 9 true (0) (by decide) cert1635 m hm
#print axioms never1635


/-- Third-level first-hole refinement 1636, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_1LB---; entry 6, period 3. -/
def p1636 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1636 : zipCycle p1636 6 3 true (2) = true := by decide +kernel
theorem never1636 (m : Machine) (hm : compatible p1636 m) : NeverHalts m :=
  zipCycle_sound p1636 6 3 true (2) (by decide) cert1636 m hm
#print axioms never1636


/-- Third-level first-hole refinement 1637, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_0RB---; entry 1, period 8. -/
def p1637 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1637 : zipCycle p1637 1 8 true (1) = true := by decide +kernel
theorem never1637 (m : Machine) (hm : compatible p1637 m) : NeverHalts m :=
  zipCycle_sound p1637 1 8 true (1) (by decide) cert1637 m hm
#print axioms never1637


/-- Third-level first-hole refinement 1638, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_1RB---; entry 1, period 8. -/
def p1638 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1638 : zipCycle p1638 1 8 true (1) = true := by decide +kernel
theorem never1638 (m : Machine) (hm : compatible p1638 m) : NeverHalts m :=
  zipCycle_sound p1638 1 8 true (1) (by decide) cert1638 m hm
#print axioms never1638


/-- Third-level first-hole refinement 1639, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_1RC---; entry 2, period 7. -/
def p1639 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1639 : zipCycle p1639 2 7 true (1) = true := by decide +kernel
theorem never1639 (m : Machine) (hm : compatible p1639 m) : NeverHalts m :=
  zipCycle_sound p1639 2 7 true (1) (by decide) cert1639 m hm
#print axioms never1639


/-- Third-level first-hole refinement 1640, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_0LD---; entry 1, period 9. -/
def p1640 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1640 : zipCycle p1640 1 9 true (1) = true := by decide +kernel
theorem never1640 (m : Machine) (hm : compatible p1640 m) : NeverHalts m :=
  zipCycle_sound p1640 1 9 true (1) (by decide) cert1640 m hm
#print axioms never1640


/-- Third-level first-hole refinement 1641, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_0RD---; entry 3, period 6. -/
def p1641 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1641 : zipCycle p1641 3 6 true (1) = true := by decide +kernel
theorem never1641 (m : Machine) (hm : compatible p1641 m) : NeverHalts m :=
  zipCycle_sound p1641 3 6 true (1) (by decide) cert1641 m hm
#print axioms never1641


/-- Third-level first-hole refinement 1642, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_0LE---; entry 7, period 2. -/
def p1642 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1642 : zipCycle p1642 7 2 true (3) = true := by decide +kernel
theorem never1642 (m : Machine) (hm : compatible p1642 m) : NeverHalts m :=
  zipCycle_sound p1642 7 2 true (3) (by decide) cert1642 m hm
#print axioms never1642


/-- Third-level first-hole refinement 1643, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_0RF---; entry 8, period 1. -/
def p1643 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,5⟩)
  | _,_ => none
theorem cert1643 : zipCycle p1643 8 1 true (4) = true := by decide +kernel
theorem never1643 (m : Machine) (hm : compatible p1643 m) : NeverHalts m :=
  zipCycle_sound p1643 8 1 true (4) (by decide) cert1643 m hm
#print axioms never1643


/-- Third-level first-hole refinement 1644, 1RB---_1RC1RE_0RD---_1LD1RB_---1RF_1RF---; entry 8, period 1. -/
def p1644 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,5⟩)
  | _,_ => none
theorem cert1644 : zipCycle p1644 8 1 true (4) = true := by decide +kernel
theorem never1644 (m : Machine) (hm : compatible p1644 m) : NeverHalts m :=
  zipCycle_sound p1644 8 1 true (4) (by decide) cert1644 m hm
#print axioms never1644

end BB6.Agent24Raw45D3_16
