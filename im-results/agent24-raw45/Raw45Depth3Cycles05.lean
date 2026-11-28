import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_05
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 500, 1RB---_1RC1LB_0RD0RE_1LD1RB_---1LD_------; entry 7, period 7. -/
def p500 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert500 : zipCycle p500 7 7 false (1) = true := by decide +kernel
theorem never500 (m : Machine) (hm : compatible p500 m) : NeverHalts m :=
  zipCycle_sound p500 7 7 false (1) (by decide) cert500 m hm
#print axioms never500


/-- Third-level first-hole refinement 501, 1RB---_1RC1LB_0RD0RE_1LD1RB_---0RD_------; entry 7, period 15. -/
def p501 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert501 : zipCycle p501 7 15 true (-1) = true := by decide +kernel
theorem never501 (m : Machine) (hm : compatible p501 m) : NeverHalts m :=
  zipCycle_sound p501 7 15 true (-1) (by decide) cert501 m hm
#print axioms never501


/-- Third-level first-hole refinement 502, 1RB---_1RC1LB_0RD0RE_1LD1RB_---1RD_------; entry 5, period 27. -/
def p502 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert502 : zipCycle p502 5 27 true (-1) = true := by decide +kernel
theorem never502 (m : Machine) (hm : compatible p502 m) : NeverHalts m :=
  zipCycle_sound p502 5 27 true (-1) (by decide) cert502 m hm
#print axioms never502


/-- Third-level first-hole refinement 503, 1RB---_1RC1LB_0RD1RE_1LD1RB_---0LB_------; entry 7, period 5. -/
def p503 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert503 : zipCycle p503 7 5 false (1) = true := by decide +kernel
theorem never503 (m : Machine) (hm : compatible p503 m) : NeverHalts m :=
  zipCycle_sound p503 7 5 false (1) (by decide) cert503 m hm
#print axioms never503


/-- Third-level first-hole refinement 504, 1RB---_1RC1LB_0RD1RE_1LD1RB_---1LB_------; entry 7, period 5. -/
def p504 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert504 : zipCycle p504 7 5 false (1) = true := by decide +kernel
theorem never504 (m : Machine) (hm : compatible p504 m) : NeverHalts m :=
  zipCycle_sound p504 7 5 false (1) (by decide) cert504 m hm
#print axioms never504


/-- Third-level first-hole refinement 505, 1RB---_1RC1LB_0RD1RE_1LD1RB_---1RB_------; entry 6, period 7. -/
def p505 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert505 : zipCycle p505 6 7 false (2) = true := by decide +kernel
theorem never505 (m : Machine) (hm : compatible p505 m) : NeverHalts m :=
  zipCycle_sound p505 6 7 false (2) (by decide) cert505 m hm
#print axioms never505


/-- Third-level first-hole refinement 506, 1RB---_1RC1LB_0RD1RE_1LD1RB_---1LC_------; entry 10, period 2. -/
def p506 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert506 : zipCycle p506 10 2 true (0) = true := by decide +kernel
theorem never506 (m : Machine) (hm : compatible p506 m) : NeverHalts m :=
  zipCycle_sound p506 10 2 true (0) (by decide) cert506 m hm
#print axioms never506


/-- Third-level first-hole refinement 507, 1RB---_1RC1LB_0RD1RE_1LD1RB_---0RC_------; entry 7, period 12. -/
def p507 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert507 : zipCycle p507 7 12 true (-1) = true := by decide +kernel
theorem never507 (m : Machine) (hm : compatible p507 m) : NeverHalts m :=
  zipCycle_sound p507 7 12 true (-1) (by decide) cert507 m hm
#print axioms never507


/-- Third-level first-hole refinement 508, 1RB---_1RC1LB_0RD1RE_1LD1RB_---1LD_------; entry 5, period 7. -/
def p508 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert508 : zipCycle p508 5 7 false (2) = true := by decide +kernel
theorem never508 (m : Machine) (hm : compatible p508 m) : NeverHalts m :=
  zipCycle_sound p508 5 7 false (2) (by decide) cert508 m hm
#print axioms never508


/-- Third-level first-hole refinement 509, 1RB---_1RC1LB_0RD1RE_1LD1RB_---1RD_------; entry 6, period 9. -/
def p509 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert509 : zipCycle p509 6 9 false (3) = true := by decide +kernel
theorem never509 (m : Machine) (hm : compatible p509 m) : NeverHalts m :=
  zipCycle_sound p509 6 9 false (3) (by decide) cert509 m hm
#print axioms never509


/-- Third-level first-hole refinement 510, 1RB0LA_1RC0LC_0RD0LA_1LD1RB_------_------; entry 0, period 9. -/
def p510 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert510 : zipCycle p510 0 9 false (3) = true := by decide +kernel
theorem never510 (m : Machine) (hm : compatible p510 m) : NeverHalts m :=
  zipCycle_sound p510 0 9 false (3) (by decide) cert510 m hm
#print axioms never510


/-- Third-level first-hole refinement 511, 1RB1LA_1RC0LC_0RD0LA_1LD1RB_------_------; entry 0, period 12. -/
def p511 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert511 : zipCycle p511 0 12 false (3) = true := by decide +kernel
theorem never511 (m : Machine) (hm : compatible p511 m) : NeverHalts m :=
  zipCycle_sound p511 0 12 false (3) (by decide) cert511 m hm
#print axioms never511


/-- Third-level first-hole refinement 512, 1RB0RA_1RC0LC_0RD0LA_1LD1RB_------_------; entry 0, period 13. -/
def p512 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert512 : zipCycle p512 0 13 true (0) = true := by decide +kernel
theorem never512 (m : Machine) (hm : compatible p512 m) : NeverHalts m :=
  zipCycle_sound p512 0 13 true (0) (by decide) cert512 m hm
#print axioms never512


/-- Third-level first-hole refinement 513, 1RB1RA_1RC0LC_0RD0LA_1LD1RB_------_------; entry 0, period 13. -/
def p513 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert513 : zipCycle p513 0 13 true (0) = true := by decide +kernel
theorem never513 (m : Machine) (hm : compatible p513 m) : NeverHalts m :=
  zipCycle_sound p513 0 13 true (0) (by decide) cert513 m hm
#print axioms never513


/-- Third-level first-hole refinement 514, 1RB0LB_1RC0LC_0RD0LA_1LD1RB_------_------; entry 2, period 22. -/
def p514 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert514 : zipCycle p514 2 22 false (3) = true := by decide +kernel
theorem never514 (m : Machine) (hm : compatible p514 m) : NeverHalts m :=
  zipCycle_sound p514 2 22 false (3) (by decide) cert514 m hm
#print axioms never514


/-- Third-level first-hole refinement 515, 1RB1LB_1RC0LC_0RD0LA_1LD1RB_------_------; entry 7, period 3. -/
def p515 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert515 : zipCycle p515 7 3 false (1) = true := by decide +kernel
theorem never515 (m : Machine) (hm : compatible p515 m) : NeverHalts m :=
  zipCycle_sound p515 7 3 false (1) (by decide) cert515 m hm
#print axioms never515


/-- Third-level first-hole refinement 516, 1RB0RB_1RC0LC_0RD0LA_1LD1RB_------_------; entry 1, period 11. -/
def p516 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert516 : zipCycle p516 1 11 true (0) = true := by decide +kernel
theorem never516 (m : Machine) (hm : compatible p516 m) : NeverHalts m :=
  zipCycle_sound p516 1 11 true (0) (by decide) cert516 m hm
#print axioms never516


/-- Third-level first-hole refinement 517, 1RB1RB_1RC0LC_0RD0LA_1LD1RB_------_------; entry 1, period 11. -/
def p517 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert517 : zipCycle p517 1 11 true (0) = true := by decide +kernel
theorem never517 (m : Machine) (hm : compatible p517 m) : NeverHalts m :=
  zipCycle_sound p517 1 11 true (0) (by decide) cert517 m hm
#print axioms never517


/-- Third-level first-hole refinement 518, 1RB0LC_1RC0LC_0RD0LA_1LD1RB_------_------; entry 10, period 1. -/
def p518 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert518 : zipCycle p518 10 1 false (0) = true := by decide +kernel
theorem never518 (m : Machine) (hm : compatible p518 m) : NeverHalts m :=
  zipCycle_sound p518 10 1 false (0) (by decide) cert518 m hm
#print axioms never518


/-- Third-level first-hole refinement 519, 1RB1LC_1RC0LC_0RD0LA_1LD1RB_------_------; entry 1, period 13. -/
def p519 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert519 : zipCycle p519 1 13 true (-1) = true := by decide +kernel
theorem never519 (m : Machine) (hm : compatible p519 m) : NeverHalts m :=
  zipCycle_sound p519 1 13 true (-1) (by decide) cert519 m hm
#print axioms never519


/-- Third-level first-hole refinement 520, 1RB0RC_1RC0LC_0RD0LA_1LD1RB_------_------; entry 10, period 1. -/
def p520 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert520 : zipCycle p520 10 1 false (2) = true := by decide +kernel
theorem never520 (m : Machine) (hm : compatible p520 m) : NeverHalts m :=
  zipCycle_sound p520 10 1 false (2) (by decide) cert520 m hm
#print axioms never520


/-- Third-level first-hole refinement 521, 1RB0LD_1RC0LC_0RD0LA_1LD1RB_------_------; entry 9, period 1. -/
def p521 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert521 : zipCycle p521 9 1 false (-1) = true := by decide +kernel
theorem never521 (m : Machine) (hm : compatible p521 m) : NeverHalts m :=
  zipCycle_sound p521 9 1 false (-1) (by decide) cert521 m hm
#print axioms never521


/-- Third-level first-hole refinement 522, 1RB1LD_1RC0LC_0RD0LA_1LD1RB_------_------; entry 9, period 1. -/
def p522 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert522 : zipCycle p522 9 1 false (-1) = true := by decide +kernel
theorem never522 (m : Machine) (hm : compatible p522 m) : NeverHalts m :=
  zipCycle_sound p522 9 1 false (-1) (by decide) cert522 m hm
#print axioms never522


/-- Third-level first-hole refinement 523, 1RB0RD_1RC0LC_0RD0LA_1LD1RB_------_------; entry 9, period 1. -/
def p523 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert523 : zipCycle p523 9 1 false (1) = true := by decide +kernel
theorem never523 (m : Machine) (hm : compatible p523 m) : NeverHalts m :=
  zipCycle_sound p523 9 1 false (1) (by decide) cert523 m hm
#print axioms never523


/-- Third-level first-hole refinement 524, 1RB1RD_1RC0LC_0RD0LA_1LD1RB_------_------; entry 0, period 13. -/
def p524 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert524 : zipCycle p524 0 13 false (3) = true := by decide +kernel
theorem never524 (m : Machine) (hm : compatible p524 m) : NeverHalts m :=
  zipCycle_sound p524 0 13 false (3) (by decide) cert524 m hm
#print axioms never524


/-- Third-level first-hole refinement 525, 1RB1LA_1RC0LC_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p525 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert525 : zipCycle p525 9 3 false (0) = true := by decide +kernel
theorem never525 (m : Machine) (hm : compatible p525 m) : NeverHalts m :=
  zipCycle_sound p525 9 3 false (0) (by decide) cert525 m hm
#print axioms never525


/-- Third-level first-hole refinement 526, 1RB0RA_1RC0LC_0RD1LA_1LD1RB_------_------; entry 10, period 3. -/
def p526 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert526 : zipCycle p526 10 3 false (3) = true := by decide +kernel
theorem never526 (m : Machine) (hm : compatible p526 m) : NeverHalts m :=
  zipCycle_sound p526 10 3 false (3) (by decide) cert526 m hm
#print axioms never526


/-- Third-level first-hole refinement 527, 1RB1RA_1RC0LC_0RD1LA_1LD1RB_------_------; entry 0, period 15. -/
def p527 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert527 : zipCycle p527 0 15 true (0) = true := by decide +kernel
theorem never527 (m : Machine) (hm : compatible p527 m) : NeverHalts m :=
  zipCycle_sound p527 0 15 true (0) (by decide) cert527 m hm
#print axioms never527


/-- Third-level first-hole refinement 528, 1RB0LB_1RC0LC_0RD1LA_1LD1RB_------_------; entry 20, period 3. -/
def p528 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert528 : zipCycle p528 20 3 false (0) = true := by decide +kernel
theorem never528 (m : Machine) (hm : compatible p528 m) : NeverHalts m :=
  zipCycle_sound p528 20 3 false (0) (by decide) cert528 m hm
#print axioms never528


/-- Third-level first-hole refinement 529, 1RB1LB_1RC0LC_0RD1LA_1LD1RB_------_------; entry 7, period 3. -/
def p529 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert529 : zipCycle p529 7 3 false (1) = true := by decide +kernel
theorem never529 (m : Machine) (hm : compatible p529 m) : NeverHalts m :=
  zipCycle_sound p529 7 3 false (1) (by decide) cert529 m hm
#print axioms never529


/-- Third-level first-hole refinement 530, 1RB0RB_1RC0LC_0RD1LA_1LD1RB_------_------; entry 11, period 1. -/
def p530 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert530 : zipCycle p530 11 1 false (1) = true := by decide +kernel
theorem never530 (m : Machine) (hm : compatible p530 m) : NeverHalts m :=
  zipCycle_sound p530 11 1 false (1) (by decide) cert530 m hm
#print axioms never530


/-- Third-level first-hole refinement 531, 1RB1RB_1RC0LC_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p531 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert531 : zipCycle p531 9 3 false (1) = true := by decide +kernel
theorem never531 (m : Machine) (hm : compatible p531 m) : NeverHalts m :=
  zipCycle_sound p531 9 3 false (1) (by decide) cert531 m hm
#print axioms never531


/-- Third-level first-hole refinement 532, 1RB0LC_1RC0LC_0RD1LA_1LD1RB_------_------; entry 10, period 1. -/
def p532 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert532 : zipCycle p532 10 1 false (0) = true := by decide +kernel
theorem never532 (m : Machine) (hm : compatible p532 m) : NeverHalts m :=
  zipCycle_sound p532 10 1 false (0) (by decide) cert532 m hm
#print axioms never532


/-- Third-level first-hole refinement 533, 1RB1LC_1RC0LC_0RD1LA_1LD1RB_------_------; entry 11, period 3. -/
def p533 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert533 : zipCycle p533 11 3 false (1) = true := by decide +kernel
theorem never533 (m : Machine) (hm : compatible p533 m) : NeverHalts m :=
  zipCycle_sound p533 11 3 false (1) (by decide) cert533 m hm
#print axioms never533


/-- Third-level first-hole refinement 534, 1RB0RC_1RC0LC_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p534 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert534 : zipCycle p534 9 3 false (1) = true := by decide +kernel
theorem never534 (m : Machine) (hm : compatible p534 m) : NeverHalts m :=
  zipCycle_sound p534 9 3 false (1) (by decide) cert534 m hm
#print axioms never534


/-- Third-level first-hole refinement 535, 1RB1RC_1RC0LC_0RD1LA_1LD1RB_------_------; entry 7, period 2. -/
def p535 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert535 : zipCycle p535 7 2 true (0) = true := by decide +kernel
theorem never535 (m : Machine) (hm : compatible p535 m) : NeverHalts m :=
  zipCycle_sound p535 7 2 true (0) (by decide) cert535 m hm
#print axioms never535


/-- Third-level first-hole refinement 536, 1RB0LD_1RC0LC_0RD1LA_1LD1RB_------_------; entry 9, period 1. -/
def p536 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert536 : zipCycle p536 9 1 false (-1) = true := by decide +kernel
theorem never536 (m : Machine) (hm : compatible p536 m) : NeverHalts m :=
  zipCycle_sound p536 9 1 false (-1) (by decide) cert536 m hm
#print axioms never536


/-- Third-level first-hole refinement 537, 1RB1LD_1RC0LC_0RD1LA_1LD1RB_------_------; entry 9, period 1. -/
def p537 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert537 : zipCycle p537 9 1 false (-1) = true := by decide +kernel
theorem never537 (m : Machine) (hm : compatible p537 m) : NeverHalts m :=
  zipCycle_sound p537 9 1 false (-1) (by decide) cert537 m hm
#print axioms never537


/-- Third-level first-hole refinement 538, 1RB0RD_1RC0LC_0RD1LA_1LD1RB_------_------; entry 1, period 13. -/
def p538 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert538 : zipCycle p538 1 13 true (0) = true := by decide +kernel
theorem never538 (m : Machine) (hm : compatible p538 m) : NeverHalts m :=
  zipCycle_sound p538 1 13 true (0) (by decide) cert538 m hm
#print axioms never538


/-- Third-level first-hole refinement 539, 1RB1RD_1RC0LC_0RD1LA_1LD1RB_------_------; entry 1, period 13. -/
def p539 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert539 : zipCycle p539 1 13 true (0) = true := by decide +kernel
theorem never539 (m : Machine) (hm : compatible p539 m) : NeverHalts m :=
  zipCycle_sound p539 1 13 true (0) (by decide) cert539 m hm
#print axioms never539


/-- Third-level first-hole refinement 540, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0LA_------; entry 0, period 9. -/
def p540 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert540 : zipCycle p540 0 9 false (3) = true := by decide +kernel
theorem never540 (m : Machine) (hm : compatible p540 m) : NeverHalts m :=
  zipCycle_sound p540 0 9 false (3) (by decide) cert540 m hm
#print axioms never540


/-- Third-level first-hole refinement 541, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0RA_------; entry 0, period 13. -/
def p541 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert541 : zipCycle p541 0 13 true (0) = true := by decide +kernel
theorem never541 (m : Machine) (hm : compatible p541 m) : NeverHalts m :=
  zipCycle_sound p541 0 13 true (0) (by decide) cert541 m hm
#print axioms never541


/-- Third-level first-hole refinement 542, 1RB---_1RC0LC_0RD0LE_1LD1RB_---1RA_------; entry 0, period 13. -/
def p542 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert542 : zipCycle p542 0 13 true (0) = true := by decide +kernel
theorem never542 (m : Machine) (hm : compatible p542 m) : NeverHalts m :=
  zipCycle_sound p542 0 13 true (0) (by decide) cert542 m hm
#print axioms never542


/-- Third-level first-hole refinement 543, 1RB---_1RC0LC_0RD0LE_1LD1RB_---1LB_------; entry 7, period 3. -/
def p543 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert543 : zipCycle p543 7 3 false (1) = true := by decide +kernel
theorem never543 (m : Machine) (hm : compatible p543 m) : NeverHalts m :=
  zipCycle_sound p543 7 3 false (1) (by decide) cert543 m hm
#print axioms never543


/-- Third-level first-hole refinement 544, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0RB_------; entry 1, period 11. -/
def p544 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert544 : zipCycle p544 1 11 true (0) = true := by decide +kernel
theorem never544 (m : Machine) (hm : compatible p544 m) : NeverHalts m :=
  zipCycle_sound p544 1 11 true (0) (by decide) cert544 m hm
#print axioms never544


/-- Third-level first-hole refinement 545, 1RB---_1RC0LC_0RD0LE_1LD1RB_---1RB_------; entry 1, period 11. -/
def p545 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert545 : zipCycle p545 1 11 true (0) = true := by decide +kernel
theorem never545 (m : Machine) (hm : compatible p545 m) : NeverHalts m :=
  zipCycle_sound p545 1 11 true (0) (by decide) cert545 m hm
#print axioms never545


/-- Third-level first-hole refinement 546, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0LC_------; entry 10, period 1. -/
def p546 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert546 : zipCycle p546 10 1 false (0) = true := by decide +kernel
theorem never546 (m : Machine) (hm : compatible p546 m) : NeverHalts m :=
  zipCycle_sound p546 10 1 false (0) (by decide) cert546 m hm
#print axioms never546


/-- Third-level first-hole refinement 547, 1RB---_1RC0LC_0RD0LE_1LD1RB_---1LC_------; entry 1, period 13. -/
def p547 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert547 : zipCycle p547 1 13 true (-1) = true := by decide +kernel
theorem never547 (m : Machine) (hm : compatible p547 m) : NeverHalts m :=
  zipCycle_sound p547 1 13 true (-1) (by decide) cert547 m hm
#print axioms never547


/-- Third-level first-hole refinement 548, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0RC_------; entry 10, period 1. -/
def p548 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert548 : zipCycle p548 10 1 false (2) = true := by decide +kernel
theorem never548 (m : Machine) (hm : compatible p548 m) : NeverHalts m :=
  zipCycle_sound p548 10 1 false (2) (by decide) cert548 m hm
#print axioms never548


/-- Third-level first-hole refinement 549, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0LD_------; entry 9, period 1. -/
def p549 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert549 : zipCycle p549 9 1 false (-1) = true := by decide +kernel
theorem never549 (m : Machine) (hm : compatible p549 m) : NeverHalts m :=
  zipCycle_sound p549 9 1 false (-1) (by decide) cert549 m hm
#print axioms never549


/-- Third-level first-hole refinement 550, 1RB---_1RC0LC_0RD0LE_1LD1RB_---1LD_------; entry 9, period 1. -/
def p550 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert550 : zipCycle p550 9 1 false (-1) = true := by decide +kernel
theorem never550 (m : Machine) (hm : compatible p550 m) : NeverHalts m :=
  zipCycle_sound p550 9 1 false (-1) (by decide) cert550 m hm
#print axioms never550


/-- Third-level first-hole refinement 551, 1RB---_1RC0LC_0RD0LE_1LD1RB_---0RD_------; entry 9, period 1. -/
def p551 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert551 : zipCycle p551 9 1 false (1) = true := by decide +kernel
theorem never551 (m : Machine) (hm : compatible p551 m) : NeverHalts m :=
  zipCycle_sound p551 9 1 false (1) (by decide) cert551 m hm
#print axioms never551


/-- Third-level first-hole refinement 552, 1RB---_1RC0LC_0RD1LE_1LD1RB_---1LB_------; entry 7, period 3. -/
def p552 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert552 : zipCycle p552 7 3 false (1) = true := by decide +kernel
theorem never552 (m : Machine) (hm : compatible p552 m) : NeverHalts m :=
  zipCycle_sound p552 7 3 false (1) (by decide) cert552 m hm
#print axioms never552


/-- Third-level first-hole refinement 553, 1RB---_1RC0LC_0RD1LE_1LD1RB_---0RB_------; entry 11, period 1. -/
def p553 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert553 : zipCycle p553 11 1 false (1) = true := by decide +kernel
theorem never553 (m : Machine) (hm : compatible p553 m) : NeverHalts m :=
  zipCycle_sound p553 11 1 false (1) (by decide) cert553 m hm
#print axioms never553


/-- Third-level first-hole refinement 554, 1RB---_1RC0LC_0RD1LE_1LD1RB_---0LC_------; entry 10, period 1. -/
def p554 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert554 : zipCycle p554 10 1 false (0) = true := by decide +kernel
theorem never554 (m : Machine) (hm : compatible p554 m) : NeverHalts m :=
  zipCycle_sound p554 10 1 false (0) (by decide) cert554 m hm
#print axioms never554


/-- Third-level first-hole refinement 555, 1RB---_1RC0LC_0RD1LE_1LD1RB_---1RC_------; entry 7, period 2. -/
def p555 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert555 : zipCycle p555 7 2 true (0) = true := by decide +kernel
theorem never555 (m : Machine) (hm : compatible p555 m) : NeverHalts m :=
  zipCycle_sound p555 7 2 true (0) (by decide) cert555 m hm
#print axioms never555


/-- Third-level first-hole refinement 556, 1RB---_1RC0LC_0RD1LE_1LD1RB_---0LD_------; entry 9, period 1. -/
def p556 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert556 : zipCycle p556 9 1 false (-1) = true := by decide +kernel
theorem never556 (m : Machine) (hm : compatible p556 m) : NeverHalts m :=
  zipCycle_sound p556 9 1 false (-1) (by decide) cert556 m hm
#print axioms never556


/-- Third-level first-hole refinement 557, 1RB---_1RC0LC_0RD1LE_1LD1RB_---1LD_------; entry 9, period 1. -/
def p557 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert557 : zipCycle p557 9 1 false (-1) = true := by decide +kernel
theorem never557 (m : Machine) (hm : compatible p557 m) : NeverHalts m :=
  zipCycle_sound p557 9 1 false (-1) (by decide) cert557 m hm
#print axioms never557


/-- Third-level first-hole refinement 558, 1RB---_1RC0LC_0RD1LE_1LD1RB_---0RD_------; entry 1, period 13. -/
def p558 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert558 : zipCycle p558 1 13 true (0) = true := by decide +kernel
theorem never558 (m : Machine) (hm : compatible p558 m) : NeverHalts m :=
  zipCycle_sound p558 1 13 true (0) (by decide) cert558 m hm
#print axioms never558


/-- Third-level first-hole refinement 559, 1RB---_1RC0LC_0RD1LE_1LD1RB_---1RD_------; entry 1, period 13. -/
def p559 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert559 : zipCycle p559 1 13 true (0) = true := by decide +kernel
theorem never559 (m : Machine) (hm : compatible p559 m) : NeverHalts m :=
  zipCycle_sound p559 1 13 true (0) (by decide) cert559 m hm
#print axioms never559


/-- Third-level first-hole refinement 560, 1RB---_1RC0LC_0RD0RE_1LD1RB_0LA---_------; entry 0, period 13. -/
def p560 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert560 : zipCycle p560 0 13 true (0) = true := by decide +kernel
theorem never560 (m : Machine) (hm : compatible p560 m) : NeverHalts m :=
  zipCycle_sound p560 0 13 true (0) (by decide) cert560 m hm
#print axioms never560


/-- Third-level first-hole refinement 561, 1RB---_1RC0LC_0RD0RE_1LD1RB_1LA---_------; entry 6, period 4. -/
def p561 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert561 : zipCycle p561 6 4 true (1) = true := by decide +kernel
theorem never561 (m : Machine) (hm : compatible p561 m) : NeverHalts m :=
  zipCycle_sound p561 6 4 true (1) (by decide) cert561 m hm
#print axioms never561


/-- Third-level first-hole refinement 562, 1RB---_1RC0LC_0RD0RE_1LD1RB_0LB---_------; entry 1, period 11. -/
def p562 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert562 : zipCycle p562 1 11 true (1) = true := by decide +kernel
theorem never562 (m : Machine) (hm : compatible p562 m) : NeverHalts m :=
  zipCycle_sound p562 1 11 true (1) (by decide) cert562 m hm
#print axioms never562


/-- Third-level first-hole refinement 563, 1RB---_1RC0LC_0RD0RE_1LD1RB_0RB---_------; entry 20, period 1. -/
def p563 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert563 : zipCycle p563 20 1 false (2) = true := by decide +kernel
theorem never563 (m : Machine) (hm : compatible p563 m) : NeverHalts m :=
  zipCycle_sound p563 20 1 false (2) (by decide) cert563 m hm
#print axioms never563


/-- Third-level first-hole refinement 564, 1RB---_1RC0LC_0RD0RE_1LD1RB_1RB---_------; entry 1, period 11. -/
def p564 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert564 : zipCycle p564 1 11 true (1) = true := by decide +kernel
theorem never564 (m : Machine) (hm : compatible p564 m) : NeverHalts m :=
  zipCycle_sound p564 1 11 true (1) (by decide) cert564 m hm
#print axioms never564


/-- Third-level first-hole refinement 565, 1RB---_1RC0LC_0RD0RE_1LD1RB_0LC---_------; entry 17, period 1. -/
def p565 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert565 : zipCycle p565 17 1 false (1) = true := by decide +kernel
theorem never565 (m : Machine) (hm : compatible p565 m) : NeverHalts m :=
  zipCycle_sound p565 17 1 false (1) (by decide) cert565 m hm
#print axioms never565


/-- Third-level first-hole refinement 566, 1RB---_1RC0LC_0RD0RE_1LD1RB_1LC---_------; entry 1, period 15. -/
def p566 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert566 : zipCycle p566 1 15 true (1) = true := by decide +kernel
theorem never566 (m : Machine) (hm : compatible p566 m) : NeverHalts m :=
  zipCycle_sound p566 1 15 true (1) (by decide) cert566 m hm
#print axioms never566


/-- Third-level first-hole refinement 567, 1RB---_1RC0LC_0RD0RE_1LD1RB_1RC---_------; entry 2, period 9. -/
def p567 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert567 : zipCycle p567 2 9 true (1) = true := by decide +kernel
theorem never567 (m : Machine) (hm : compatible p567 m) : NeverHalts m :=
  zipCycle_sound p567 2 9 true (1) (by decide) cert567 m hm
#print axioms never567


/-- Third-level first-hole refinement 568, 1RB---_1RC0LC_0RD0RE_1LD1RB_0LD---_------; entry 14, period 1. -/
def p568 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert568 : zipCycle p568 14 1 false (0) = true := by decide +kernel
theorem never568 (m : Machine) (hm : compatible p568 m) : NeverHalts m :=
  zipCycle_sound p568 14 1 false (0) (by decide) cert568 m hm
#print axioms never568


/-- Third-level first-hole refinement 569, 1RB---_1RC0LC_0RD0RE_1LD1RB_1LD---_------; entry 14, period 1. -/
def p569 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert569 : zipCycle p569 14 1 false (0) = true := by decide +kernel
theorem never569 (m : Machine) (hm : compatible p569 m) : NeverHalts m :=
  zipCycle_sound p569 14 1 false (0) (by decide) cert569 m hm
#print axioms never569


/-- Third-level first-hole refinement 570, 1RB---_1RC0LC_0RD0RE_1LD1RB_0RD---_------; entry 1, period 9. -/
def p570 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert570 : zipCycle p570 1 9 true (1) = true := by decide +kernel
theorem never570 (m : Machine) (hm : compatible p570 m) : NeverHalts m :=
  zipCycle_sound p570 1 9 true (1) (by decide) cert570 m hm
#print axioms never570


/-- Third-level first-hole refinement 571, 1RB---_1RC0LC_0RD0RE_1LD1RB_1RD---_------; entry 1, period 9. -/
def p571 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert571 : zipCycle p571 1 9 true (1) = true := by decide +kernel
theorem never571 (m : Machine) (hm : compatible p571 m) : NeverHalts m :=
  zipCycle_sound p571 1 9 true (1) (by decide) cert571 m hm
#print axioms never571


/-- Third-level first-hole refinement 572, 1RB---_1RC0LC_0RD1RE_1LD1RB_0LB---_------; entry 14, period 1. -/
def p572 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert572 : zipCycle p572 14 1 false (0) = true := by decide +kernel
theorem never572 (m : Machine) (hm : compatible p572 m) : NeverHalts m :=
  zipCycle_sound p572 14 1 false (0) (by decide) cert572 m hm
#print axioms never572


/-- Third-level first-hole refinement 573, 1RB---_1RC0LC_0RD1RE_1LD1RB_1LB---_------; entry 14, period 1. -/
def p573 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert573 : zipCycle p573 14 1 false (0) = true := by decide +kernel
theorem never573 (m : Machine) (hm : compatible p573 m) : NeverHalts m :=
  zipCycle_sound p573 14 1 false (0) (by decide) cert573 m hm
#print axioms never573


/-- Third-level first-hole refinement 574, 1RB---_1RC0LC_0RD1RE_1LD1RB_0RB---_------; entry 2, period 8. -/
def p574 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert574 : zipCycle p574 2 8 true (1) = true := by decide +kernel
theorem never574 (m : Machine) (hm : compatible p574 m) : NeverHalts m :=
  zipCycle_sound p574 2 8 true (1) (by decide) cert574 m hm
#print axioms never574


/-- Third-level first-hole refinement 575, 1RB---_1RC0LC_0RD1RE_1LD1RB_1RB---_------; entry 1, period 11. -/
def p575 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert575 : zipCycle p575 1 11 true (1) = true := by decide +kernel
theorem never575 (m : Machine) (hm : compatible p575 m) : NeverHalts m :=
  zipCycle_sound p575 1 11 true (1) (by decide) cert575 m hm
#print axioms never575


/-- Third-level first-hole refinement 576, 1RB---_1RC0LC_0RD1RE_1LD1RB_0LC---_------; entry 7, period 2. -/
def p576 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert576 : zipCycle p576 7 2 true (1) = true := by decide +kernel
theorem never576 (m : Machine) (hm : compatible p576 m) : NeverHalts m :=
  zipCycle_sound p576 7 2 true (1) (by decide) cert576 m hm
#print axioms never576


/-- Third-level first-hole refinement 577, 1RB---_1RC0LC_0RD1RE_1LD1RB_1RC---_------; entry 2, period 9. -/
def p577 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert577 : zipCycle p577 2 9 true (1) = true := by decide +kernel
theorem never577 (m : Machine) (hm : compatible p577 m) : NeverHalts m :=
  zipCycle_sound p577 2 9 true (1) (by decide) cert577 m hm
#print axioms never577


/-- Third-level first-hole refinement 578, 1RB---_1RC0LC_0RD1RE_1LD1RB_0LD---_------; entry 1, period 13. -/
def p578 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert578 : zipCycle p578 1 13 true (1) = true := by decide +kernel
theorem never578 (m : Machine) (hm : compatible p578 m) : NeverHalts m :=
  zipCycle_sound p578 1 13 true (1) (by decide) cert578 m hm
#print axioms never578


/-- Third-level first-hole refinement 579, 1RB---_1RC0LC_0RD1RE_1LD1RB_1LD---_------; entry 5, period 4. -/
def p579 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert579 : zipCycle p579 5 4 true (1) = true := by decide +kernel
theorem never579 (m : Machine) (hm : compatible p579 m) : NeverHalts m :=
  zipCycle_sound p579 5 4 true (1) (by decide) cert579 m hm
#print axioms never579


/-- Third-level first-hole refinement 580, 1RB---_1RC0LC_0RD1RE_1LD1RB_0RD---_------; entry 1, period 9. -/
def p580 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert580 : zipCycle p580 1 9 true (1) = true := by decide +kernel
theorem never580 (m : Machine) (hm : compatible p580 m) : NeverHalts m :=
  zipCycle_sound p580 1 9 true (1) (by decide) cert580 m hm
#print axioms never580


/-- Third-level first-hole refinement 581, 1RB---_1RC0LC_0RD1RE_1LD1RB_1RD---_------; entry 1, period 9. -/
def p581 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert581 : zipCycle p581 1 9 true (1) = true := by decide +kernel
theorem never581 (m : Machine) (hm : compatible p581 m) : NeverHalts m :=
  zipCycle_sound p581 1 9 true (1) (by decide) cert581 m hm
#print axioms never581


/-- Third-level first-hole refinement 582, 1RB0LA_1RC1LC_0RD0LA_1LD1RB_------_------; entry 0, period 22. -/
def p582 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert582 : zipCycle p582 0 22 false (3) = true := by decide +kernel
theorem never582 (m : Machine) (hm : compatible p582 m) : NeverHalts m :=
  zipCycle_sound p582 0 22 false (3) (by decide) cert582 m hm
#print axioms never582


/-- Third-level first-hole refinement 583, 1RB1LA_1RC1LC_0RD0LA_1LD1RB_------_------; entry 8, period 8. -/
def p583 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert583 : zipCycle p583 8 8 false (0) = true := by decide +kernel
theorem never583 (m : Machine) (hm : compatible p583 m) : NeverHalts m :=
  zipCycle_sound p583 8 8 false (0) (by decide) cert583 m hm
#print axioms never583


/-- Third-level first-hole refinement 584, 1RB0RA_1RC1LC_0RD0LA_1LD1RB_------_------; entry 0, period 23. -/
def p584 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert584 : zipCycle p584 0 23 true (0) = true := by decide +kernel
theorem never584 (m : Machine) (hm : compatible p584 m) : NeverHalts m :=
  zipCycle_sound p584 0 23 true (0) (by decide) cert584 m hm
#print axioms never584


/-- Third-level first-hole refinement 585, 1RB1RA_1RC1LC_0RD0LA_1LD1RB_------_------; entry 6, period 4. -/
def p585 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert585 : zipCycle p585 6 4 true (0) = true := by decide +kernel
theorem never585 (m : Machine) (hm : compatible p585 m) : NeverHalts m :=
  zipCycle_sound p585 6 4 true (0) (by decide) cert585 m hm
#print axioms never585


/-- Third-level first-hole refinement 586, 1RB0LB_1RC1LC_0RD0LA_1LD1RB_------_------; entry 6, period 26. -/
def p586 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert586 : zipCycle p586 6 26 false (2) = true := by decide +kernel
theorem never586 (m : Machine) (hm : compatible p586 m) : NeverHalts m :=
  zipCycle_sound p586 6 26 false (2) (by decide) cert586 m hm
#print axioms never586


/-- Third-level first-hole refinement 587, 1RB1LB_1RC1LC_0RD0LA_1LD1RB_------_------; entry 7, period 3. -/
def p587 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert587 : zipCycle p587 7 3 false (1) = true := by decide +kernel
theorem never587 (m : Machine) (hm : compatible p587 m) : NeverHalts m :=
  zipCycle_sound p587 7 3 false (1) (by decide) cert587 m hm
#print axioms never587


/-- Third-level first-hole refinement 588, 1RB0RB_1RC1LC_0RD0LA_1LD1RB_------_------; entry 9, period 14. -/
def p588 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert588 : zipCycle p588 9 14 true (1) = true := by decide +kernel
theorem never588 (m : Machine) (hm : compatible p588 m) : NeverHalts m :=
  zipCycle_sound p588 9 14 true (1) (by decide) cert588 m hm
#print axioms never588


/-- Third-level first-hole refinement 589, 1RB1RB_1RC1LC_0RD0LA_1LD1RB_------_------; entry 1, period 14. -/
def p589 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert589 : zipCycle p589 1 14 true (0) = true := by decide +kernel
theorem never589 (m : Machine) (hm : compatible p589 m) : NeverHalts m :=
  zipCycle_sound p589 1 14 true (0) (by decide) cert589 m hm
#print axioms never589


/-- Third-level first-hole refinement 590, 1RB0LC_1RC1LC_0RD0LA_1LD1RB_------_------; entry 10, period 1. -/
def p590 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert590 : zipCycle p590 10 1 false (0) = true := by decide +kernel
theorem never590 (m : Machine) (hm : compatible p590 m) : NeverHalts m :=
  zipCycle_sound p590 10 1 false (0) (by decide) cert590 m hm
#print axioms never590


/-- Third-level first-hole refinement 591, 1RB1LC_1RC1LC_0RD0LA_1LD1RB_------_------; entry 11, period 5. -/
def p591 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert591 : zipCycle p591 11 5 false (2) = true := by decide +kernel
theorem never591 (m : Machine) (hm : compatible p591 m) : NeverHalts m :=
  zipCycle_sound p591 11 5 false (2) (by decide) cert591 m hm
#print axioms never591


/-- Third-level first-hole refinement 592, 1RB0RC_1RC1LC_0RD0LA_1LD1RB_------_------; entry 7, period 19. -/
def p592 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert592 : zipCycle p592 7 19 true (0) = true := by decide +kernel
theorem never592 (m : Machine) (hm : compatible p592 m) : NeverHalts m :=
  zipCycle_sound p592 7 19 true (0) (by decide) cert592 m hm
#print axioms never592


/-- Third-level first-hole refinement 593, 1RB1RC_1RC1LC_0RD0LA_1LD1RB_------_------; entry 2, period 15. -/
def p593 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert593 : zipCycle p593 2 15 true (0) = true := by decide +kernel
theorem never593 (m : Machine) (hm : compatible p593 m) : NeverHalts m :=
  zipCycle_sound p593 2 15 true (0) (by decide) cert593 m hm
#print axioms never593


/-- Third-level first-hole refinement 594, 1RB0LD_1RC1LC_0RD0LA_1LD1RB_------_------; entry 9, period 1. -/
def p594 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert594 : zipCycle p594 9 1 false (-1) = true := by decide +kernel
theorem never594 (m : Machine) (hm : compatible p594 m) : NeverHalts m :=
  zipCycle_sound p594 9 1 false (-1) (by decide) cert594 m hm
#print axioms never594


/-- Third-level first-hole refinement 595, 1RB1LD_1RC1LC_0RD0LA_1LD1RB_------_------; entry 9, period 1. -/
def p595 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert595 : zipCycle p595 9 1 false (-1) = true := by decide +kernel
theorem never595 (m : Machine) (hm : compatible p595 m) : NeverHalts m :=
  zipCycle_sound p595 9 1 false (-1) (by decide) cert595 m hm
#print axioms never595


/-- Third-level first-hole refinement 596, 1RB0RD_1RC1LC_0RD0LA_1LD1RB_------_------; entry 9, period 1. -/
def p596 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert596 : zipCycle p596 9 1 false (1) = true := by decide +kernel
theorem never596 (m : Machine) (hm : compatible p596 m) : NeverHalts m :=
  zipCycle_sound p596 9 1 false (1) (by decide) cert596 m hm
#print axioms never596


/-- Third-level first-hole refinement 597, 1RB1RD_1RC1LC_0RD0LA_1LD1RB_------_------; entry 4, period 13. -/
def p597 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert597 : zipCycle p597 4 13 false (2) = true := by decide +kernel
theorem never597 (m : Machine) (hm : compatible p597 m) : NeverHalts m :=
  zipCycle_sound p597 4 13 false (2) (by decide) cert597 m hm
#print axioms never597


/-- Third-level first-hole refinement 598, 1RB0LA_1RC1LC_0RD1LA_1LD1RB_------_------; entry 11, period 11. -/
def p598 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert598 : zipCycle p598 11 11 false (2) = true := by decide +kernel
theorem never598 (m : Machine) (hm : compatible p598 m) : NeverHalts m :=
  zipCycle_sound p598 11 11 false (2) (by decide) cert598 m hm
#print axioms never598


/-- Third-level first-hole refinement 599, 1RB1LA_1RC1LC_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p599 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert599 : zipCycle p599 9 3 false (0) = true := by decide +kernel
theorem never599 (m : Machine) (hm : compatible p599 m) : NeverHalts m :=
  zipCycle_sound p599 9 3 false (0) (by decide) cert599 m hm
#print axioms never599

end BB6.Agent24Raw45D3_05
