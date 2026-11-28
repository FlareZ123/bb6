import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_06
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 600, 1RB0RA_1RC1LC_0RD1LA_1LD1RB_------_------; entry 0, period 12. -/
def p600 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert600 : zipCycle p600 0 12 true (0) = true := by decide +kernel
theorem never600 (m : Machine) (hm : compatible p600 m) : NeverHalts m :=
  zipCycle_sound p600 0 12 true (0) (by decide) cert600 m hm
#print axioms never600


/-- Third-level first-hole refinement 601, 1RB1RA_1RC1LC_0RD1LA_1LD1RB_------_------; entry 0, period 12. -/
def p601 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert601 : zipCycle p601 0 12 true (0) = true := by decide +kernel
theorem never601 (m : Machine) (hm : compatible p601 m) : NeverHalts m :=
  zipCycle_sound p601 0 12 true (0) (by decide) cert601 m hm
#print axioms never601


/-- Third-level first-hole refinement 602, 1RB0LB_1RC1LC_0RD1LA_1LD1RB_------_------; entry 6, period 9. -/
def p602 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert602 : zipCycle p602 6 9 false (2) = true := by decide +kernel
theorem never602 (m : Machine) (hm : compatible p602 m) : NeverHalts m :=
  zipCycle_sound p602 6 9 false (2) (by decide) cert602 m hm
#print axioms never602


/-- Third-level first-hole refinement 603, 1RB1LB_1RC1LC_0RD1LA_1LD1RB_------_------; entry 7, period 3. -/
def p603 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert603 : zipCycle p603 7 3 false (1) = true := by decide +kernel
theorem never603 (m : Machine) (hm : compatible p603 m) : NeverHalts m :=
  zipCycle_sound p603 7 3 false (1) (by decide) cert603 m hm
#print axioms never603


/-- Third-level first-hole refinement 604, 1RB0RB_1RC1LC_0RD1LA_1LD1RB_------_------; entry 12, period 3. -/
def p604 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert604 : zipCycle p604 12 3 false (2) = true := by decide +kernel
theorem never604 (m : Machine) (hm : compatible p604 m) : NeverHalts m :=
  zipCycle_sound p604 12 3 false (2) (by decide) cert604 m hm
#print axioms never604


/-- Third-level first-hole refinement 605, 1RB1RB_1RC1LC_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p605 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert605 : zipCycle p605 9 3 false (1) = true := by decide +kernel
theorem never605 (m : Machine) (hm : compatible p605 m) : NeverHalts m :=
  zipCycle_sound p605 9 3 false (1) (by decide) cert605 m hm
#print axioms never605


/-- Third-level first-hole refinement 606, 1RB0LC_1RC1LC_0RD1LA_1LD1RB_------_------; entry 10, period 1. -/
def p606 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert606 : zipCycle p606 10 1 false (0) = true := by decide +kernel
theorem never606 (m : Machine) (hm : compatible p606 m) : NeverHalts m :=
  zipCycle_sound p606 10 1 false (0) (by decide) cert606 m hm
#print axioms never606


/-- Third-level first-hole refinement 607, 1RB1LC_1RC1LC_0RD1LA_1LD1RB_------_------; entry 11, period 3. -/
def p607 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert607 : zipCycle p607 11 3 false (1) = true := by decide +kernel
theorem never607 (m : Machine) (hm : compatible p607 m) : NeverHalts m :=
  zipCycle_sound p607 11 3 false (1) (by decide) cert607 m hm
#print axioms never607


/-- Third-level first-hole refinement 608, 1RB0RC_1RC1LC_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p608 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert608 : zipCycle p608 9 3 false (1) = true := by decide +kernel
theorem never608 (m : Machine) (hm : compatible p608 m) : NeverHalts m :=
  zipCycle_sound p608 9 3 false (1) (by decide) cert608 m hm
#print axioms never608


/-- Third-level first-hole refinement 609, 1RB1RC_1RC1LC_0RD1LA_1LD1RB_------_------; entry 7, period 2. -/
def p609 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert609 : zipCycle p609 7 2 true (0) = true := by decide +kernel
theorem never609 (m : Machine) (hm : compatible p609 m) : NeverHalts m :=
  zipCycle_sound p609 7 2 true (0) (by decide) cert609 m hm
#print axioms never609


/-- Third-level first-hole refinement 610, 1RB0LD_1RC1LC_0RD1LA_1LD1RB_------_------; entry 9, period 1. -/
def p610 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert610 : zipCycle p610 9 1 false (-1) = true := by decide +kernel
theorem never610 (m : Machine) (hm : compatible p610 m) : NeverHalts m :=
  zipCycle_sound p610 9 1 false (-1) (by decide) cert610 m hm
#print axioms never610


/-- Third-level first-hole refinement 611, 1RB1LD_1RC1LC_0RD1LA_1LD1RB_------_------; entry 9, period 1. -/
def p611 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert611 : zipCycle p611 9 1 false (-1) = true := by decide +kernel
theorem never611 (m : Machine) (hm : compatible p611 m) : NeverHalts m :=
  zipCycle_sound p611 9 1 false (-1) (by decide) cert611 m hm
#print axioms never611


/-- Third-level first-hole refinement 612, 1RB0RD_1RC1LC_0RD1LA_1LD1RB_------_------; entry 10, period 3. -/
def p612 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert612 : zipCycle p612 10 3 false (2) = true := by decide +kernel
theorem never612 (m : Machine) (hm : compatible p612 m) : NeverHalts m :=
  zipCycle_sound p612 10 3 false (2) (by decide) cert612 m hm
#print axioms never612


/-- Third-level first-hole refinement 613, 1RB1RD_1RC1LC_0RD1LA_1LD1RB_------_------; entry 5, period 4. -/
def p613 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert613 : zipCycle p613 5 4 true (0) = true := by decide +kernel
theorem never613 (m : Machine) (hm : compatible p613 m) : NeverHalts m :=
  zipCycle_sound p613 5 4 true (0) (by decide) cert613 m hm
#print axioms never613


/-- Third-level first-hole refinement 614, 1RB0LA_1RC1LC_0RD0RA_1LD1RB_------_------; entry 0, period 12. -/
def p614 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert614 : zipCycle p614 0 12 true (0) = true := by decide +kernel
theorem never614 (m : Machine) (hm : compatible p614 m) : NeverHalts m :=
  zipCycle_sound p614 0 12 true (0) (by decide) cert614 m hm
#print axioms never614


/-- Third-level first-hole refinement 615, 1RB1LA_1RC1LC_0RD0RA_1LD1RB_------_------; entry 6, period 4. -/
def p615 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert615 : zipCycle p615 6 4 true (1) = true := by decide +kernel
theorem never615 (m : Machine) (hm : compatible p615 m) : NeverHalts m :=
  zipCycle_sound p615 6 4 true (1) (by decide) cert615 m hm
#print axioms never615


/-- Third-level first-hole refinement 616, 1RB0RA_1RC1LC_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p616 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert616 : zipCycle p616 0 10 true (0) = true := by decide +kernel
theorem never616 (m : Machine) (hm : compatible p616 m) : NeverHalts m :=
  zipCycle_sound p616 0 10 true (0) (by decide) cert616 m hm
#print axioms never616


/-- Third-level first-hole refinement 617, 1RB1RA_1RC1LC_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p617 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert617 : zipCycle p617 0 10 true (0) = true := by decide +kernel
theorem never617 (m : Machine) (hm : compatible p617 m) : NeverHalts m :=
  zipCycle_sound p617 0 10 true (0) (by decide) cert617 m hm
#print axioms never617


/-- Third-level first-hole refinement 618, 1RB0LB_1RC1LC_0RD0RA_1LD1RB_------_------; entry 1, period 11. -/
def p618 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert618 : zipCycle p618 1 11 true (1) = true := by decide +kernel
theorem never618 (m : Machine) (hm : compatible p618 m) : NeverHalts m :=
  zipCycle_sound p618 1 11 true (1) (by decide) cert618 m hm
#print axioms never618


/-- Third-level first-hole refinement 619, 1RB1LB_1RC1LC_0RD0RA_1LD1RB_------_------; entry 0, period 14. -/
def p619 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert619 : zipCycle p619 0 14 true (0) = true := by decide +kernel
theorem never619 (m : Machine) (hm : compatible p619 m) : NeverHalts m :=
  zipCycle_sound p619 0 14 true (0) (by decide) cert619 m hm
#print axioms never619


/-- Third-level first-hole refinement 620, 1RB0RB_1RC1LC_0RD0RA_1LD1RB_------_------; entry 1, period 11. -/
def p620 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert620 : zipCycle p620 1 11 true (1) = true := by decide +kernel
theorem never620 (m : Machine) (hm : compatible p620 m) : NeverHalts m :=
  zipCycle_sound p620 1 11 true (1) (by decide) cert620 m hm
#print axioms never620


/-- Third-level first-hole refinement 621, 1RB1RB_1RC1LC_0RD0RA_1LD1RB_------_------; entry 1, period 11. -/
def p621 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert621 : zipCycle p621 1 11 true (1) = true := by decide +kernel
theorem never621 (m : Machine) (hm : compatible p621 m) : NeverHalts m :=
  zipCycle_sound p621 1 11 true (1) (by decide) cert621 m hm
#print axioms never621


/-- Third-level first-hole refinement 622, 1RB0LC_1RC1LC_0RD0RA_1LD1RB_------_------; entry 17, period 1. -/
def p622 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert622 : zipCycle p622 17 1 false (1) = true := by decide +kernel
theorem never622 (m : Machine) (hm : compatible p622 m) : NeverHalts m :=
  zipCycle_sound p622 17 1 false (1) (by decide) cert622 m hm
#print axioms never622


/-- Third-level first-hole refinement 623, 1RB1LC_1RC1LC_0RD0RA_1LD1RB_------_------; entry 1, period 15. -/
def p623 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert623 : zipCycle p623 1 15 true (1) = true := by decide +kernel
theorem never623 (m : Machine) (hm : compatible p623 m) : NeverHalts m :=
  zipCycle_sound p623 1 15 true (1) (by decide) cert623 m hm
#print axioms never623


/-- Third-level first-hole refinement 624, 1RB0RC_1RC1LC_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p624 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert624 : zipCycle p624 0 10 true (0) = true := by decide +kernel
theorem never624 (m : Machine) (hm : compatible p624 m) : NeverHalts m :=
  zipCycle_sound p624 0 10 true (0) (by decide) cert624 m hm
#print axioms never624


/-- Third-level first-hole refinement 625, 1RB1RC_1RC1LC_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p625 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert625 : zipCycle p625 0 10 true (0) = true := by decide +kernel
theorem never625 (m : Machine) (hm : compatible p625 m) : NeverHalts m :=
  zipCycle_sound p625 0 10 true (0) (by decide) cert625 m hm
#print axioms never625


/-- Third-level first-hole refinement 626, 1RB0LD_1RC1LC_0RD0RA_1LD1RB_------_------; entry 14, period 1. -/
def p626 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert626 : zipCycle p626 14 1 false (0) = true := by decide +kernel
theorem never626 (m : Machine) (hm : compatible p626 m) : NeverHalts m :=
  zipCycle_sound p626 14 1 false (0) (by decide) cert626 m hm
#print axioms never626


/-- Third-level first-hole refinement 627, 1RB1LD_1RC1LC_0RD0RA_1LD1RB_------_------; entry 14, period 1. -/
def p627 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert627 : zipCycle p627 14 1 false (0) = true := by decide +kernel
theorem never627 (m : Machine) (hm : compatible p627 m) : NeverHalts m :=
  zipCycle_sound p627 14 1 false (0) (by decide) cert627 m hm
#print axioms never627


/-- Third-level first-hole refinement 628, 1RB0RD_1RC1LC_0RD0RA_1LD1RB_------_------; entry 1, period 9. -/
def p628 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert628 : zipCycle p628 1 9 true (1) = true := by decide +kernel
theorem never628 (m : Machine) (hm : compatible p628 m) : NeverHalts m :=
  zipCycle_sound p628 1 9 true (1) (by decide) cert628 m hm
#print axioms never628


/-- Third-level first-hole refinement 629, 1RB1RD_1RC1LC_0RD0RA_1LD1RB_------_------; entry 1, period 9. -/
def p629 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert629 : zipCycle p629 1 9 true (1) = true := by decide +kernel
theorem never629 (m : Machine) (hm : compatible p629 m) : NeverHalts m :=
  zipCycle_sound p629 1 9 true (1) (by decide) cert629 m hm
#print axioms never629


/-- Third-level first-hole refinement 630, 1RB0LA_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 11. -/
def p630 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert630 : zipCycle p630 0 11 false (3) = true := by decide +kernel
theorem never630 (m : Machine) (hm : compatible p630 m) : NeverHalts m :=
  zipCycle_sound p630 0 11 false (3) (by decide) cert630 m hm
#print axioms never630


/-- Third-level first-hole refinement 631, 1RB1LA_1RC1LC_0RD1RA_1LD1RB_------_------; entry 9, period 5. -/
def p631 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert631 : zipCycle p631 9 5 false (1) = true := by decide +kernel
theorem never631 (m : Machine) (hm : compatible p631 m) : NeverHalts m :=
  zipCycle_sound p631 9 5 false (1) (by decide) cert631 m hm
#print axioms never631


/-- Third-level first-hole refinement 632, 1RB0RA_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p632 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert632 : zipCycle p632 0 10 true (0) = true := by decide +kernel
theorem never632 (m : Machine) (hm : compatible p632 m) : NeverHalts m :=
  zipCycle_sound p632 0 10 true (0) (by decide) cert632 m hm
#print axioms never632


/-- Third-level first-hole refinement 633, 1RB1RA_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p633 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert633 : zipCycle p633 0 10 true (0) = true := by decide +kernel
theorem never633 (m : Machine) (hm : compatible p633 m) : NeverHalts m :=
  zipCycle_sound p633 0 10 true (0) (by decide) cert633 m hm
#print axioms never633


/-- Third-level first-hole refinement 634, 1RB0LB_1RC1LC_0RD1RA_1LD1RB_------_------; entry 1, period 17. -/
def p634 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert634 : zipCycle p634 1 17 true (-1) = true := by decide +kernel
theorem never634 (m : Machine) (hm : compatible p634 m) : NeverHalts m :=
  zipCycle_sound p634 1 17 true (-1) (by decide) cert634 m hm
#print axioms never634


/-- Third-level first-hole refinement 635, 1RB1LB_1RC1LC_0RD1RA_1LD1RB_------_------; entry 9, period 6. -/
def p635 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert635 : zipCycle p635 9 6 true (-1) = true := by decide +kernel
theorem never635 (m : Machine) (hm : compatible p635 m) : NeverHalts m :=
  zipCycle_sound p635 9 6 true (-1) (by decide) cert635 m hm
#print axioms never635


/-- Third-level first-hole refinement 636, 1RB0RB_1RC1LC_0RD1RA_1LD1RB_------_------; entry 1, period 11. -/
def p636 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert636 : zipCycle p636 1 11 true (1) = true := by decide +kernel
theorem never636 (m : Machine) (hm : compatible p636 m) : NeverHalts m :=
  zipCycle_sound p636 1 11 true (1) (by decide) cert636 m hm
#print axioms never636


/-- Third-level first-hole refinement 637, 1RB1RB_1RC1LC_0RD1RA_1LD1RB_------_------; entry 1, period 11. -/
def p637 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert637 : zipCycle p637 1 11 true (1) = true := by decide +kernel
theorem never637 (m : Machine) (hm : compatible p637 m) : NeverHalts m :=
  zipCycle_sound p637 1 11 true (1) (by decide) cert637 m hm
#print axioms never637


/-- Third-level first-hole refinement 638, 1RB0LC_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 15. -/
def p638 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert638 : zipCycle p638 0 15 true (0) = true := by decide +kernel
theorem never638 (m : Machine) (hm : compatible p638 m) : NeverHalts m :=
  zipCycle_sound p638 0 15 true (0) (by decide) cert638 m hm
#print axioms never638


/-- Third-level first-hole refinement 639, 1RB1LC_1RC1LC_0RD1RA_1LD1RB_------_------; entry 7, period 2. -/
def p639 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert639 : zipCycle p639 7 2 true (1) = true := by decide +kernel
theorem never639 (m : Machine) (hm : compatible p639 m) : NeverHalts m :=
  zipCycle_sound p639 7 2 true (1) (by decide) cert639 m hm
#print axioms never639


/-- Third-level first-hole refinement 640, 1RB0RC_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p640 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert640 : zipCycle p640 0 10 true (0) = true := by decide +kernel
theorem never640 (m : Machine) (hm : compatible p640 m) : NeverHalts m :=
  zipCycle_sound p640 0 10 true (0) (by decide) cert640 m hm
#print axioms never640


/-- Third-level first-hole refinement 641, 1RB1RC_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p641 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert641 : zipCycle p641 0 10 true (0) = true := by decide +kernel
theorem never641 (m : Machine) (hm : compatible p641 m) : NeverHalts m :=
  zipCycle_sound p641 0 10 true (0) (by decide) cert641 m hm
#print axioms never641


/-- Third-level first-hole refinement 642, 1RB0LD_1RC1LC_0RD1RA_1LD1RB_------_------; entry 0, period 12. -/
def p642 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert642 : zipCycle p642 0 12 true (0) = true := by decide +kernel
theorem never642 (m : Machine) (hm : compatible p642 m) : NeverHalts m :=
  zipCycle_sound p642 0 12 true (0) (by decide) cert642 m hm
#print axioms never642


/-- Third-level first-hole refinement 643, 1RB1LD_1RC1LC_0RD1RA_1LD1RB_------_------; entry 5, period 4. -/
def p643 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert643 : zipCycle p643 5 4 true (1) = true := by decide +kernel
theorem never643 (m : Machine) (hm : compatible p643 m) : NeverHalts m :=
  zipCycle_sound p643 5 4 true (1) (by decide) cert643 m hm
#print axioms never643


/-- Third-level first-hole refinement 644, 1RB0RD_1RC1LC_0RD1RA_1LD1RB_------_------; entry 1, period 9. -/
def p644 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert644 : zipCycle p644 1 9 true (1) = true := by decide +kernel
theorem never644 (m : Machine) (hm : compatible p644 m) : NeverHalts m :=
  zipCycle_sound p644 1 9 true (1) (by decide) cert644 m hm
#print axioms never644


/-- Third-level first-hole refinement 645, 1RB1RD_1RC1LC_0RD1RA_1LD1RB_------_------; entry 1, period 9. -/
def p645 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert645 : zipCycle p645 1 9 true (1) = true := by decide +kernel
theorem never645 (m : Machine) (hm : compatible p645 m) : NeverHalts m :=
  zipCycle_sound p645 1 9 true (1) (by decide) cert645 m hm
#print axioms never645


/-- Third-level first-hole refinement 646, 1RB---_1RC1LC_0RD0LE_1LD1RB_---1RA_------; entry 6, period 4. -/
def p646 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert646 : zipCycle p646 6 4 true (0) = true := by decide +kernel
theorem never646 (m : Machine) (hm : compatible p646 m) : NeverHalts m :=
  zipCycle_sound p646 6 4 true (0) (by decide) cert646 m hm
#print axioms never646


/-- Third-level first-hole refinement 647, 1RB---_1RC1LC_0RD0LE_1LD1RB_---1LB_------; entry 7, period 3. -/
def p647 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert647 : zipCycle p647 7 3 false (1) = true := by decide +kernel
theorem never647 (m : Machine) (hm : compatible p647 m) : NeverHalts m :=
  zipCycle_sound p647 7 3 false (1) (by decide) cert647 m hm
#print axioms never647


/-- Third-level first-hole refinement 648, 1RB---_1RC1LC_0RD0LE_1LD1RB_---1RB_------; entry 1, period 14. -/
def p648 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert648 : zipCycle p648 1 14 true (0) = true := by decide +kernel
theorem never648 (m : Machine) (hm : compatible p648 m) : NeverHalts m :=
  zipCycle_sound p648 1 14 true (0) (by decide) cert648 m hm
#print axioms never648


/-- Third-level first-hole refinement 649, 1RB---_1RC1LC_0RD0LE_1LD1RB_---0LC_------; entry 10, period 1. -/
def p649 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert649 : zipCycle p649 10 1 false (0) = true := by decide +kernel
theorem never649 (m : Machine) (hm : compatible p649 m) : NeverHalts m :=
  zipCycle_sound p649 10 1 false (0) (by decide) cert649 m hm
#print axioms never649


/-- Third-level first-hole refinement 650, 1RB---_1RC1LC_0RD0LE_1LD1RB_---0LD_------; entry 9, period 1. -/
def p650 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert650 : zipCycle p650 9 1 false (-1) = true := by decide +kernel
theorem never650 (m : Machine) (hm : compatible p650 m) : NeverHalts m :=
  zipCycle_sound p650 9 1 false (-1) (by decide) cert650 m hm
#print axioms never650


/-- Third-level first-hole refinement 651, 1RB---_1RC1LC_0RD0LE_1LD1RB_---1LD_------; entry 9, period 1. -/
def p651 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert651 : zipCycle p651 9 1 false (-1) = true := by decide +kernel
theorem never651 (m : Machine) (hm : compatible p651 m) : NeverHalts m :=
  zipCycle_sound p651 9 1 false (-1) (by decide) cert651 m hm
#print axioms never651


/-- Third-level first-hole refinement 652, 1RB---_1RC1LC_0RD0LE_1LD1RB_---0RD_------; entry 9, period 1. -/
def p652 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert652 : zipCycle p652 9 1 false (1) = true := by decide +kernel
theorem never652 (m : Machine) (hm : compatible p652 m) : NeverHalts m :=
  zipCycle_sound p652 9 1 false (1) (by decide) cert652 m hm
#print axioms never652


/-- Third-level first-hole refinement 653, 1RB---_1RC1LC_0RD1LE_1LD1RB_---1LB_------; entry 7, period 3. -/
def p653 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert653 : zipCycle p653 7 3 false (1) = true := by decide +kernel
theorem never653 (m : Machine) (hm : compatible p653 m) : NeverHalts m :=
  zipCycle_sound p653 7 3 false (1) (by decide) cert653 m hm
#print axioms never653


/-- Third-level first-hole refinement 654, 1RB---_1RC1LC_0RD1LE_1LD1RB_---0LC_------; entry 10, period 1. -/
def p654 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert654 : zipCycle p654 10 1 false (0) = true := by decide +kernel
theorem never654 (m : Machine) (hm : compatible p654 m) : NeverHalts m :=
  zipCycle_sound p654 10 1 false (0) (by decide) cert654 m hm
#print axioms never654


/-- Third-level first-hole refinement 655, 1RB---_1RC1LC_0RD1LE_1LD1RB_---1RC_------; entry 7, period 2. -/
def p655 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert655 : zipCycle p655 7 2 true (0) = true := by decide +kernel
theorem never655 (m : Machine) (hm : compatible p655 m) : NeverHalts m :=
  zipCycle_sound p655 7 2 true (0) (by decide) cert655 m hm
#print axioms never655


/-- Third-level first-hole refinement 656, 1RB---_1RC1LC_0RD1LE_1LD1RB_---0LD_------; entry 9, period 1. -/
def p656 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert656 : zipCycle p656 9 1 false (-1) = true := by decide +kernel
theorem never656 (m : Machine) (hm : compatible p656 m) : NeverHalts m :=
  zipCycle_sound p656 9 1 false (-1) (by decide) cert656 m hm
#print axioms never656


/-- Third-level first-hole refinement 657, 1RB---_1RC1LC_0RD1LE_1LD1RB_---1LD_------; entry 9, period 1. -/
def p657 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert657 : zipCycle p657 9 1 false (-1) = true := by decide +kernel
theorem never657 (m : Machine) (hm : compatible p657 m) : NeverHalts m :=
  zipCycle_sound p657 9 1 false (-1) (by decide) cert657 m hm
#print axioms never657


/-- Third-level first-hole refinement 658, 1RB---_1RC1LC_0RD1LE_1LD1RB_---1RD_------; entry 5, period 4. -/
def p658 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert658 : zipCycle p658 5 4 true (0) = true := by decide +kernel
theorem never658 (m : Machine) (hm : compatible p658 m) : NeverHalts m :=
  zipCycle_sound p658 5 4 true (0) (by decide) cert658 m hm
#print axioms never658


/-- Third-level first-hole refinement 659, 1RB---_1RC1LC_0RD0RE_1LD1RB_---1LA_------; entry 6, period 4. -/
def p659 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert659 : zipCycle p659 6 4 true (1) = true := by decide +kernel
theorem never659 (m : Machine) (hm : compatible p659 m) : NeverHalts m :=
  zipCycle_sound p659 6 4 true (1) (by decide) cert659 m hm
#print axioms never659


/-- Third-level first-hole refinement 660, 1RB---_1RC1LC_0RD0RE_1LD1RB_---0LB_------; entry 1, period 11. -/
def p660 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert660 : zipCycle p660 1 11 true (1) = true := by decide +kernel
theorem never660 (m : Machine) (hm : compatible p660 m) : NeverHalts m :=
  zipCycle_sound p660 1 11 true (1) (by decide) cert660 m hm
#print axioms never660


/-- Third-level first-hole refinement 661, 1RB---_1RC1LC_0RD0RE_1LD1RB_---0RB_------; entry 1, period 11. -/
def p661 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert661 : zipCycle p661 1 11 true (1) = true := by decide +kernel
theorem never661 (m : Machine) (hm : compatible p661 m) : NeverHalts m :=
  zipCycle_sound p661 1 11 true (1) (by decide) cert661 m hm
#print axioms never661


/-- Third-level first-hole refinement 662, 1RB---_1RC1LC_0RD0RE_1LD1RB_---1RB_------; entry 1, period 11. -/
def p662 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert662 : zipCycle p662 1 11 true (1) = true := by decide +kernel
theorem never662 (m : Machine) (hm : compatible p662 m) : NeverHalts m :=
  zipCycle_sound p662 1 11 true (1) (by decide) cert662 m hm
#print axioms never662


/-- Third-level first-hole refinement 663, 1RB---_1RC1LC_0RD0RE_1LD1RB_---0LC_------; entry 17, period 1. -/
def p663 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert663 : zipCycle p663 17 1 false (1) = true := by decide +kernel
theorem never663 (m : Machine) (hm : compatible p663 m) : NeverHalts m :=
  zipCycle_sound p663 17 1 false (1) (by decide) cert663 m hm
#print axioms never663


/-- Third-level first-hole refinement 664, 1RB---_1RC1LC_0RD0RE_1LD1RB_---1LC_------; entry 1, period 15. -/
def p664 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert664 : zipCycle p664 1 15 true (1) = true := by decide +kernel
theorem never664 (m : Machine) (hm : compatible p664 m) : NeverHalts m :=
  zipCycle_sound p664 1 15 true (1) (by decide) cert664 m hm
#print axioms never664


/-- Third-level first-hole refinement 665, 1RB---_1RC1LC_0RD0RE_1LD1RB_---0LD_------; entry 14, period 1. -/
def p665 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert665 : zipCycle p665 14 1 false (0) = true := by decide +kernel
theorem never665 (m : Machine) (hm : compatible p665 m) : NeverHalts m :=
  zipCycle_sound p665 14 1 false (0) (by decide) cert665 m hm
#print axioms never665


/-- Third-level first-hole refinement 666, 1RB---_1RC1LC_0RD0RE_1LD1RB_---1LD_------; entry 14, period 1. -/
def p666 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert666 : zipCycle p666 14 1 false (0) = true := by decide +kernel
theorem never666 (m : Machine) (hm : compatible p666 m) : NeverHalts m :=
  zipCycle_sound p666 14 1 false (0) (by decide) cert666 m hm
#print axioms never666


/-- Third-level first-hole refinement 667, 1RB---_1RC1LC_0RD0RE_1LD1RB_---0RD_------; entry 1, period 9. -/
def p667 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert667 : zipCycle p667 1 9 true (1) = true := by decide +kernel
theorem never667 (m : Machine) (hm : compatible p667 m) : NeverHalts m :=
  zipCycle_sound p667 1 9 true (1) (by decide) cert667 m hm
#print axioms never667


/-- Third-level first-hole refinement 668, 1RB---_1RC1LC_0RD0RE_1LD1RB_---1RD_------; entry 1, period 9. -/
def p668 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert668 : zipCycle p668 1 9 true (1) = true := by decide +kernel
theorem never668 (m : Machine) (hm : compatible p668 m) : NeverHalts m :=
  zipCycle_sound p668 1 9 true (1) (by decide) cert668 m hm
#print axioms never668


/-- Third-level first-hole refinement 669, 1RB---_1RC1LC_0RD1RE_1LD1RB_---0LB_------; entry 1, period 17. -/
def p669 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert669 : zipCycle p669 1 17 true (-1) = true := by decide +kernel
theorem never669 (m : Machine) (hm : compatible p669 m) : NeverHalts m :=
  zipCycle_sound p669 1 17 true (-1) (by decide) cert669 m hm
#print axioms never669


/-- Third-level first-hole refinement 670, 1RB---_1RC1LC_0RD1RE_1LD1RB_---1LB_------; entry 9, period 6. -/
def p670 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert670 : zipCycle p670 9 6 true (-1) = true := by decide +kernel
theorem never670 (m : Machine) (hm : compatible p670 m) : NeverHalts m :=
  zipCycle_sound p670 9 6 true (-1) (by decide) cert670 m hm
#print axioms never670


/-- Third-level first-hole refinement 671, 1RB---_1RC1LC_0RD1RE_1LD1RB_---0RB_------; entry 1, period 11. -/
def p671 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert671 : zipCycle p671 1 11 true (1) = true := by decide +kernel
theorem never671 (m : Machine) (hm : compatible p671 m) : NeverHalts m :=
  zipCycle_sound p671 1 11 true (1) (by decide) cert671 m hm
#print axioms never671


/-- Third-level first-hole refinement 672, 1RB---_1RC1LC_0RD1RE_1LD1RB_---1RB_------; entry 1, period 11. -/
def p672 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert672 : zipCycle p672 1 11 true (1) = true := by decide +kernel
theorem never672 (m : Machine) (hm : compatible p672 m) : NeverHalts m :=
  zipCycle_sound p672 1 11 true (1) (by decide) cert672 m hm
#print axioms never672


/-- Third-level first-hole refinement 673, 1RB---_1RC1LC_0RD1RE_1LD1RB_---1LC_------; entry 7, period 2. -/
def p673 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert673 : zipCycle p673 7 2 true (1) = true := by decide +kernel
theorem never673 (m : Machine) (hm : compatible p673 m) : NeverHalts m :=
  zipCycle_sound p673 7 2 true (1) (by decide) cert673 m hm
#print axioms never673


/-- Third-level first-hole refinement 674, 1RB---_1RC1LC_0RD1RE_1LD1RB_---1LD_------; entry 5, period 4. -/
def p674 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert674 : zipCycle p674 5 4 true (1) = true := by decide +kernel
theorem never674 (m : Machine) (hm : compatible p674 m) : NeverHalts m :=
  zipCycle_sound p674 5 4 true (1) (by decide) cert674 m hm
#print axioms never674


/-- Third-level first-hole refinement 675, 1RB---_1RC1LC_0RD1RE_1LD1RB_---0RD_------; entry 1, period 9. -/
def p675 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert675 : zipCycle p675 1 9 true (1) = true := by decide +kernel
theorem never675 (m : Machine) (hm : compatible p675 m) : NeverHalts m :=
  zipCycle_sound p675 1 9 true (1) (by decide) cert675 m hm
#print axioms never675


/-- Third-level first-hole refinement 676, 1RB---_1RC1LC_0RD1RE_1LD1RB_---1RD_------; entry 1, period 9. -/
def p676 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert676 : zipCycle p676 1 9 true (1) = true := by decide +kernel
theorem never676 (m : Machine) (hm : compatible p676 m) : NeverHalts m :=
  zipCycle_sound p676 1 9 true (1) (by decide) cert676 m hm
#print axioms never676


/-- Third-level first-hole refinement 677, 1RB---_1RC0RC_0RD0LE_1LD1RB_0RA---_------; entry 0, period 9. -/
def p677 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert677 : zipCycle p677 0 9 true (0) = true := by decide +kernel
theorem never677 (m : Machine) (hm : compatible p677 m) : NeverHalts m :=
  zipCycle_sound p677 0 9 true (0) (by decide) cert677 m hm
#print axioms never677


/-- Third-level first-hole refinement 678, 1RB---_1RC0RC_0RD0LE_1LD1RB_1RA---_------; entry 0, period 9. -/
def p678 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert678 : zipCycle p678 0 9 true (0) = true := by decide +kernel
theorem never678 (m : Machine) (hm : compatible p678 m) : NeverHalts m :=
  zipCycle_sound p678 0 9 true (0) (by decide) cert678 m hm
#print axioms never678


/-- Third-level first-hole refinement 679, 1RB---_1RC0RC_0RD0LE_1LD1RB_0LB---_------; entry 20, period 1. -/
def p679 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert679 : zipCycle p679 20 1 false (2) = true := by decide +kernel
theorem never679 (m : Machine) (hm : compatible p679 m) : NeverHalts m :=
  zipCycle_sound p679 20 1 false (2) (by decide) cert679 m hm
#print axioms never679


/-- Third-level first-hole refinement 680, 1RB---_1RC0RC_0RD0LE_1LD1RB_0RB---_------; entry 1, period 8. -/
def p680 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert680 : zipCycle p680 1 8 true (1) = true := by decide +kernel
theorem never680 (m : Machine) (hm : compatible p680 m) : NeverHalts m :=
  zipCycle_sound p680 1 8 true (1) (by decide) cert680 m hm
#print axioms never680


/-- Third-level first-hole refinement 681, 1RB---_1RC0RC_0RD0LE_1LD1RB_1RB---_------; entry 1, period 8. -/
def p681 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert681 : zipCycle p681 1 8 true (1) = true := by decide +kernel
theorem never681 (m : Machine) (hm : compatible p681 m) : NeverHalts m :=
  zipCycle_sound p681 1 8 true (1) (by decide) cert681 m hm
#print axioms never681


/-- Third-level first-hole refinement 682, 1RB---_1RC0RC_0RD0LE_1LD1RB_0RC---_------; entry 1, period 18. -/
def p682 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert682 : zipCycle p682 1 18 true (1) = true := by decide +kernel
theorem never682 (m : Machine) (hm : compatible p682 m) : NeverHalts m :=
  zipCycle_sound p682 1 18 true (1) (by decide) cert682 m hm
#print axioms never682


/-- Third-level first-hole refinement 683, 1RB---_1RC0RC_0RD0LE_1LD1RB_1RC---_------; entry 2, period 7. -/
def p683 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert683 : zipCycle p683 2 7 true (1) = true := by decide +kernel
theorem never683 (m : Machine) (hm : compatible p683 m) : NeverHalts m :=
  zipCycle_sound p683 2 7 true (1) (by decide) cert683 m hm
#print axioms never683


/-- Third-level first-hole refinement 684, 1RB---_1RC0RC_0RD0LE_1LD1RB_0LD---_------; entry 1, period 9. -/
def p684 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert684 : zipCycle p684 1 9 true (1) = true := by decide +kernel
theorem never684 (m : Machine) (hm : compatible p684 m) : NeverHalts m :=
  zipCycle_sound p684 1 9 true (1) (by decide) cert684 m hm
#print axioms never684


/-- Third-level first-hole refinement 685, 1RB---_1RC0RC_0RD0LE_1LD1RB_1LD---_------; entry 1, period 22. -/
def p685 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert685 : zipCycle p685 1 22 true (1) = true := by decide +kernel
theorem never685 (m : Machine) (hm : compatible p685 m) : NeverHalts m :=
  zipCycle_sound p685 1 22 true (1) (by decide) cert685 m hm
#print axioms never685


/-- Third-level first-hole refinement 686, 1RB---_1RC0RC_0RD0LE_1LD1RB_0RD---_------; entry 3, period 6. -/
def p686 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert686 : zipCycle p686 3 6 true (1) = true := by decide +kernel
theorem never686 (m : Machine) (hm : compatible p686 m) : NeverHalts m :=
  zipCycle_sound p686 3 6 true (1) (by decide) cert686 m hm
#print axioms never686


/-- Third-level first-hole refinement 687, 1RB---_1RC0RC_0RD0LE_1LD1RB_1RD---_------; entry 4, period 16. -/
def p687 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert687 : zipCycle p687 4 16 true (1) = true := by decide +kernel
theorem never687 (m : Machine) (hm : compatible p687 m) : NeverHalts m :=
  zipCycle_sound p687 4 16 true (1) (by decide) cert687 m hm
#print axioms never687


/-- Third-level first-hole refinement 688, 1RB---_1RC0RC_0RD0LE_1LD1RB_0RE---_------; entry 8, period 1. -/
def p688 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert688 : zipCycle p688 8 1 true (2) = true := by decide +kernel
theorem never688 (m : Machine) (hm : compatible p688 m) : NeverHalts m :=
  zipCycle_sound p688 8 1 true (2) (by decide) cert688 m hm
#print axioms never688


/-- Third-level first-hole refinement 689, 1RB---_1RC0RC_0RD0LE_1LD1RB_1RE---_------; entry 8, period 1. -/
def p689 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert689 : zipCycle p689 8 1 true (2) = true := by decide +kernel
theorem never689 (m : Machine) (hm : compatible p689 m) : NeverHalts m :=
  zipCycle_sound p689 8 1 true (2) (by decide) cert689 m hm
#print axioms never689


/-- Third-level first-hole refinement 690, 1RB---_1RC0RC_0RD1LE_1LD1RB_0LB---_------; entry 1, period 11. -/
def p690 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert690 : zipCycle p690 1 11 true (1) = true := by decide +kernel
theorem never690 (m : Machine) (hm : compatible p690 m) : NeverHalts m :=
  zipCycle_sound p690 1 11 true (1) (by decide) cert690 m hm
#print axioms never690


/-- Third-level first-hole refinement 691, 1RB---_1RC0RC_0RD1LE_1LD1RB_1RB---_------; entry 6, period 12. -/
def p691 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert691 : zipCycle p691 6 12 true (2) = true := by decide +kernel
theorem never691 (m : Machine) (hm : compatible p691 m) : NeverHalts m :=
  zipCycle_sound p691 6 12 true (2) (by decide) cert691 m hm
#print axioms never691


/-- Third-level first-hole refinement 692, 1RB---_1RC0RC_0RD1LE_1LD1RB_0RC---_------; entry 7, period 2. -/
def p692 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert692 : zipCycle p692 7 2 true (2) = true := by decide +kernel
theorem never692 (m : Machine) (hm : compatible p692 m) : NeverHalts m :=
  zipCycle_sound p692 7 2 true (2) (by decide) cert692 m hm
#print axioms never692


/-- Third-level first-hole refinement 693, 1RB---_1RC0RC_0RD1LE_1LD1RB_1LD---_------; entry 5, period 4. -/
def p693 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert693 : zipCycle p693 5 4 true (1) = true := by decide +kernel
theorem never693 (m : Machine) (hm : compatible p693 m) : NeverHalts m :=
  zipCycle_sound p693 5 4 true (1) (by decide) cert693 m hm
#print axioms never693


/-- Third-level first-hole refinement 694, 1RB---_1RC0RC_0RD1LE_1LD1RB_0RD---_------; entry 1, period 9. -/
def p694 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert694 : zipCycle p694 1 9 true (1) = true := by decide +kernel
theorem never694 (m : Machine) (hm : compatible p694 m) : NeverHalts m :=
  zipCycle_sound p694 1 9 true (1) (by decide) cert694 m hm
#print axioms never694


/-- Third-level first-hole refinement 695, 1RB---_1RC0RC_0RD1LE_1LD1RB_1RD---_------; entry 1, period 9. -/
def p695 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert695 : zipCycle p695 1 9 true (1) = true := by decide +kernel
theorem never695 (m : Machine) (hm : compatible p695 m) : NeverHalts m :=
  zipCycle_sound p695 1 9 true (1) (by decide) cert695 m hm
#print axioms never695


/-- Third-level first-hole refinement 696, 1RB---_1RC0RC_0RD0RE_1LD1RB_0LA---_------; entry 0, period 9. -/
def p696 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert696 : zipCycle p696 0 9 true (0) = true := by decide +kernel
theorem never696 (m : Machine) (hm : compatible p696 m) : NeverHalts m :=
  zipCycle_sound p696 0 9 true (0) (by decide) cert696 m hm
#print axioms never696


/-- Third-level first-hole refinement 697, 1RB---_1RC0RC_0RD0RE_1LD1RB_0RA---_------; entry 0, period 9. -/
def p697 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert697 : zipCycle p697 0 9 true (0) = true := by decide +kernel
theorem never697 (m : Machine) (hm : compatible p697 m) : NeverHalts m :=
  zipCycle_sound p697 0 9 true (0) (by decide) cert697 m hm
#print axioms never697


/-- Third-level first-hole refinement 698, 1RB---_1RC0RC_0RD0RE_1LD1RB_1RA---_------; entry 0, period 9. -/
def p698 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert698 : zipCycle p698 0 9 true (0) = true := by decide +kernel
theorem never698 (m : Machine) (hm : compatible p698 m) : NeverHalts m :=
  zipCycle_sound p698 0 9 true (0) (by decide) cert698 m hm
#print axioms never698


/-- Third-level first-hole refinement 699, 1RB---_1RC0RC_0RD0RE_1LD1RB_0LB---_------; entry 1, period 8. -/
def p699 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert699 : zipCycle p699 1 8 true (1) = true := by decide +kernel
theorem never699 (m : Machine) (hm : compatible p699 m) : NeverHalts m :=
  zipCycle_sound p699 1 8 true (1) (by decide) cert699 m hm
#print axioms never699

end BB6.Agent24Raw45D3_06
