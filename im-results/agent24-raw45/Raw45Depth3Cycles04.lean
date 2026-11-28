import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_04
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 400, 1RB0RE_1RC1RA_0RD---_1LD1RB_0RE---_------; entry 8, period 1. -/
def p400 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert400 : zipCycle p400 8 1 true (4) = true := by decide +kernel
theorem never400 (m : Machine) (hm : compatible p400 m) : NeverHalts m :=
  zipCycle_sound p400 8 1 true (4) (by decide) cert400 m hm
#print axioms never400


/-- Third-level first-hole refinement 401, 1RB0RE_1RC1RA_0RD---_1LD1RB_1RE---_------; entry 8, period 1. -/
def p401 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert401 : zipCycle p401 8 1 true (4) = true := by decide +kernel
theorem never401 (m : Machine) (hm : compatible p401 m) : NeverHalts m :=
  zipCycle_sound p401 8 1 true (4) (by decide) cert401 m hm
#print axioms never401


/-- Third-level first-hole refinement 402, 1RB1RE_1RC1RA_0RD---_1LD1RB_0LA---_------; entry 7, period 2. -/
def p402 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert402 : zipCycle p402 7 2 true (3) = true := by decide +kernel
theorem never402 (m : Machine) (hm : compatible p402 m) : NeverHalts m :=
  zipCycle_sound p402 7 2 true (3) (by decide) cert402 m hm
#print axioms never402


/-- Third-level first-hole refinement 403, 1RB1RE_1RC1RA_0RD---_1LD1RB_0RA---_------; entry 0, period 9. -/
def p403 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert403 : zipCycle p403 0 9 true (0) = true := by decide +kernel
theorem never403 (m : Machine) (hm : compatible p403 m) : NeverHalts m :=
  zipCycle_sound p403 0 9 true (0) (by decide) cert403 m hm
#print axioms never403


/-- Third-level first-hole refinement 404, 1RB1RE_1RC1RA_0RD---_1LD1RB_1RA---_------; entry 0, period 9. -/
def p404 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert404 : zipCycle p404 0 9 true (0) = true := by decide +kernel
theorem never404 (m : Machine) (hm : compatible p404 m) : NeverHalts m :=
  zipCycle_sound p404 0 9 true (0) (by decide) cert404 m hm
#print axioms never404


/-- Third-level first-hole refinement 405, 1RB1RE_1RC1RA_0RD---_1LD1RB_0LB---_------; entry 0, period 10. -/
def p405 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert405 : zipCycle p405 0 10 true (0) = true := by decide +kernel
theorem never405 (m : Machine) (hm : compatible p405 m) : NeverHalts m :=
  zipCycle_sound p405 0 10 true (0) (by decide) cert405 m hm
#print axioms never405


/-- Third-level first-hole refinement 406, 1RB1RE_1RC1RA_0RD---_1LD1RB_1LB---_------; entry 6, period 3. -/
def p406 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert406 : zipCycle p406 6 3 true (2) = true := by decide +kernel
theorem never406 (m : Machine) (hm : compatible p406 m) : NeverHalts m :=
  zipCycle_sound p406 6 3 true (2) (by decide) cert406 m hm
#print axioms never406


/-- Third-level first-hole refinement 407, 1RB1RE_1RC1RA_0RD---_1LD1RB_0RB---_------; entry 1, period 8. -/
def p407 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert407 : zipCycle p407 1 8 true (1) = true := by decide +kernel
theorem never407 (m : Machine) (hm : compatible p407 m) : NeverHalts m :=
  zipCycle_sound p407 1 8 true (1) (by decide) cert407 m hm
#print axioms never407


/-- Third-level first-hole refinement 408, 1RB1RE_1RC1RA_0RD---_1LD1RB_1RB---_------; entry 1, period 8. -/
def p408 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert408 : zipCycle p408 1 8 true (1) = true := by decide +kernel
theorem never408 (m : Machine) (hm : compatible p408 m) : NeverHalts m :=
  zipCycle_sound p408 1 8 true (1) (by decide) cert408 m hm
#print axioms never408


/-- Third-level first-hole refinement 409, 1RB1RE_1RC1RA_0RD---_1LD1RB_1RC---_------; entry 2, period 7. -/
def p409 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert409 : zipCycle p409 2 7 true (1) = true := by decide +kernel
theorem never409 (m : Machine) (hm : compatible p409 m) : NeverHalts m :=
  zipCycle_sound p409 2 7 true (1) (by decide) cert409 m hm
#print axioms never409


/-- Third-level first-hole refinement 410, 1RB1RE_1RC1RA_0RD---_1LD1RB_0LD---_------; entry 1, period 9. -/
def p410 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert410 : zipCycle p410 1 9 true (1) = true := by decide +kernel
theorem never410 (m : Machine) (hm : compatible p410 m) : NeverHalts m :=
  zipCycle_sound p410 1 9 true (1) (by decide) cert410 m hm
#print axioms never410


/-- Third-level first-hole refinement 411, 1RB1RE_1RC1RA_0RD---_1LD1RB_1LD---_------; entry 0, period 11. -/
def p411 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert411 : zipCycle p411 0 11 true (0) = true := by decide +kernel
theorem never411 (m : Machine) (hm : compatible p411 m) : NeverHalts m :=
  zipCycle_sound p411 0 11 true (0) (by decide) cert411 m hm
#print axioms never411


/-- Third-level first-hole refinement 412, 1RB1RE_1RC1RA_0RD---_1LD1RB_0RD---_------; entry 3, period 6. -/
def p412 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert412 : zipCycle p412 3 6 true (1) = true := by decide +kernel
theorem never412 (m : Machine) (hm : compatible p412 m) : NeverHalts m :=
  zipCycle_sound p412 3 6 true (1) (by decide) cert412 m hm
#print axioms never412


/-- Third-level first-hole refinement 413, 1RB1RE_1RC1RA_0RD---_1LD1RB_1RD---_------; entry 0, period 12. -/
def p413 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert413 : zipCycle p413 0 12 true (0) = true := by decide +kernel
theorem never413 (m : Machine) (hm : compatible p413 m) : NeverHalts m :=
  zipCycle_sound p413 0 12 true (0) (by decide) cert413 m hm
#print axioms never413


/-- Third-level first-hole refinement 414, 1RB1RE_1RC1RA_0RD---_1LD1RB_0RE---_------; entry 8, period 1. -/
def p414 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert414 : zipCycle p414 8 1 true (4) = true := by decide +kernel
theorem never414 (m : Machine) (hm : compatible p414 m) : NeverHalts m :=
  zipCycle_sound p414 8 1 true (4) (by decide) cert414 m hm
#print axioms never414


/-- Third-level first-hole refinement 415, 1RB1RE_1RC1RA_0RD---_1LD1RB_1RE---_------; entry 8, period 1. -/
def p415 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert415 : zipCycle p415 8 1 true (4) = true := by decide +kernel
theorem never415 (m : Machine) (hm : compatible p415 m) : NeverHalts m :=
  zipCycle_sound p415 8 1 true (4) (by decide) cert415 m hm
#print axioms never415


/-- Third-level first-hole refinement 416, 1RB0LA_1RC1LB_0RD0LA_1LD1RB_------_------; entry 0, period 23. -/
def p416 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert416 : zipCycle p416 0 23 false (3) = true := by decide +kernel
theorem never416 (m : Machine) (hm : compatible p416 m) : NeverHalts m :=
  zipCycle_sound p416 0 23 false (3) (by decide) cert416 m hm
#print axioms never416


/-- Third-level first-hole refinement 417, 1RB1LA_1RC1LB_0RD0LA_1LD1RB_------_------; entry 7, period 6. -/
def p417 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert417 : zipCycle p417 7 6 false (1) = true := by decide +kernel
theorem never417 (m : Machine) (hm : compatible p417 m) : NeverHalts m :=
  zipCycle_sound p417 7 6 false (1) (by decide) cert417 m hm
#print axioms never417


/-- Third-level first-hole refinement 418, 1RB0RA_1RC1LB_0RD0LA_1LD1RB_------_------; entry 7, period 6. -/
def p418 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert418 : zipCycle p418 7 6 true (-1) = true := by decide +kernel
theorem never418 (m : Machine) (hm : compatible p418 m) : NeverHalts m :=
  zipCycle_sound p418 7 6 true (-1) (by decide) cert418 m hm
#print axioms never418


/-- Third-level first-hole refinement 419, 1RB1RA_1RC1LB_0RD0LA_1LD1RB_------_------; entry 6, period 7. -/
def p419 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert419 : zipCycle p419 6 7 false (2) = true := by decide +kernel
theorem never419 (m : Machine) (hm : compatible p419 m) : NeverHalts m :=
  zipCycle_sound p419 6 7 false (2) (by decide) cert419 m hm
#print axioms never419


/-- Third-level first-hole refinement 420, 1RB0LB_1RC1LB_0RD0LA_1LD1RB_------_------; entry 7, period 10. -/
def p420 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert420 : zipCycle p420 7 10 false (1) = true := by decide +kernel
theorem never420 (m : Machine) (hm : compatible p420 m) : NeverHalts m :=
  zipCycle_sound p420 7 10 false (1) (by decide) cert420 m hm
#print axioms never420


/-- Third-level first-hole refinement 421, 1RB1LB_1RC1LB_0RD0LA_1LD1RB_------_------; entry 9, period 3. -/
def p421 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert421 : zipCycle p421 9 3 false (0) = true := by decide +kernel
theorem never421 (m : Machine) (hm : compatible p421 m) : NeverHalts m :=
  zipCycle_sound p421 9 3 false (0) (by decide) cert421 m hm
#print axioms never421


/-- Third-level first-hole refinement 422, 1RB0RB_1RC1LB_0RD0LA_1LD1RB_------_------; entry 12, period 16. -/
def p422 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert422 : zipCycle p422 12 16 true (0) = true := by decide +kernel
theorem never422 (m : Machine) (hm : compatible p422 m) : NeverHalts m :=
  zipCycle_sound p422 12 16 true (0) (by decide) cert422 m hm
#print axioms never422


/-- Third-level first-hole refinement 423, 1RB0LC_1RC1LB_0RD0LA_1LD1RB_------_------; entry 13, period 1. -/
def p423 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert423 : zipCycle p423 13 1 false (-1) = true := by decide +kernel
theorem never423 (m : Machine) (hm : compatible p423 m) : NeverHalts m :=
  zipCycle_sound p423 13 1 false (-1) (by decide) cert423 m hm
#print axioms never423


/-- Third-level first-hole refinement 424, 1RB1LC_1RC1LB_0RD0LA_1LD1RB_------_------; entry 14, period 5. -/
def p424 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert424 : zipCycle p424 14 5 false (1) = true := by decide +kernel
theorem never424 (m : Machine) (hm : compatible p424 m) : NeverHalts m :=
  zipCycle_sound p424 14 5 false (1) (by decide) cert424 m hm
#print axioms never424


/-- Third-level first-hole refinement 425, 1RB0RC_1RC1LB_0RD0LA_1LD1RB_------_------; entry 1, period 27. -/
def p425 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert425 : zipCycle p425 1 27 true (-1) = true := by decide +kernel
theorem never425 (m : Machine) (hm : compatible p425 m) : NeverHalts m :=
  zipCycle_sound p425 1 27 true (-1) (by decide) cert425 m hm
#print axioms never425


/-- Third-level first-hole refinement 426, 1RB1RC_1RC1LB_0RD0LA_1LD1RB_------_------; entry 1, period 27. -/
def p426 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert426 : zipCycle p426 1 27 true (-1) = true := by decide +kernel
theorem never426 (m : Machine) (hm : compatible p426 m) : NeverHalts m :=
  zipCycle_sound p426 1 27 true (-1) (by decide) cert426 m hm
#print axioms never426


/-- Third-level first-hole refinement 427, 1RB0LD_1RC1LB_0RD0LA_1LD1RB_------_------; entry 12, period 1. -/
def p427 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert427 : zipCycle p427 12 1 false (-2) = true := by decide +kernel
theorem never427 (m : Machine) (hm : compatible p427 m) : NeverHalts m :=
  zipCycle_sound p427 12 1 false (-2) (by decide) cert427 m hm
#print axioms never427


/-- Third-level first-hole refinement 428, 1RB1LD_1RC1LB_0RD0LA_1LD1RB_------_------; entry 12, period 1. -/
def p428 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert428 : zipCycle p428 12 1 false (-2) = true := by decide +kernel
theorem never428 (m : Machine) (hm : compatible p428 m) : NeverHalts m :=
  zipCycle_sound p428 12 1 false (-2) (by decide) cert428 m hm
#print axioms never428


/-- Third-level first-hole refinement 429, 1RB0RD_1RC1LB_0RD0LA_1LD1RB_------_------; entry 12, period 1. -/
def p429 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert429 : zipCycle p429 12 1 false (0) = true := by decide +kernel
theorem never429 (m : Machine) (hm : compatible p429 m) : NeverHalts m :=
  zipCycle_sound p429 12 1 false (0) (by decide) cert429 m hm
#print axioms never429


/-- Third-level first-hole refinement 430, 1RB1RD_1RC1LB_0RD0LA_1LD1RB_------_------; entry 7, period 7. -/
def p430 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert430 : zipCycle p430 7 7 false (1) = true := by decide +kernel
theorem never430 (m : Machine) (hm : compatible p430 m) : NeverHalts m :=
  zipCycle_sound p430 7 7 false (1) (by decide) cert430 m hm
#print axioms never430


/-- Third-level first-hole refinement 431, 1RB0LA_1RC1LB_0RD1LA_1LD1RB_------_------; entry 0, period 28. -/
def p431 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert431 : zipCycle p431 0 28 false (3) = true := by decide +kernel
theorem never431 (m : Machine) (hm : compatible p431 m) : NeverHalts m :=
  zipCycle_sound p431 0 28 false (3) (by decide) cert431 m hm
#print axioms never431


/-- Third-level first-hole refinement 432, 1RB1LA_1RC1LB_0RD1LA_1LD1RB_------_------; entry 7, period 6. -/
def p432 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert432 : zipCycle p432 7 6 false (1) = true := by decide +kernel
theorem never432 (m : Machine) (hm : compatible p432 m) : NeverHalts m :=
  zipCycle_sound p432 7 6 false (1) (by decide) cert432 m hm
#print axioms never432


/-- Third-level first-hole refinement 433, 1RB0RA_1RC1LB_0RD1LA_1LD1RB_------_------; entry 0, period 16. -/
def p433 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert433 : zipCycle p433 0 16 true (-1) = true := by decide +kernel
theorem never433 (m : Machine) (hm : compatible p433 m) : NeverHalts m :=
  zipCycle_sound p433 0 16 true (-1) (by decide) cert433 m hm
#print axioms never433


/-- Third-level first-hole refinement 434, 1RB0LB_1RC1LB_0RD1LA_1LD1RB_------_------; entry 16, period 14. -/
def p434 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert434 : zipCycle p434 16 14 false (0) = true := by decide +kernel
theorem never434 (m : Machine) (hm : compatible p434 m) : NeverHalts m :=
  zipCycle_sound p434 16 14 false (0) (by decide) cert434 m hm
#print axioms never434


/-- Third-level first-hole refinement 435, 1RB1LB_1RC1LB_0RD1LA_1LD1RB_------_------; entry 9, period 3. -/
def p435 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert435 : zipCycle p435 9 3 false (0) = true := by decide +kernel
theorem never435 (m : Machine) (hm : compatible p435 m) : NeverHalts m :=
  zipCycle_sound p435 9 3 false (0) (by decide) cert435 m hm
#print axioms never435


/-- Third-level first-hole refinement 436, 1RB0RB_1RC1LB_0RD1LA_1LD1RB_------_------; entry 8, period 4. -/
def p436 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert436 : zipCycle p436 8 4 true (-1) = true := by decide +kernel
theorem never436 (m : Machine) (hm : compatible p436 m) : NeverHalts m :=
  zipCycle_sound p436 8 4 true (-1) (by decide) cert436 m hm
#print axioms never436


/-- Third-level first-hole refinement 437, 1RB1RB_1RC1LB_0RD1LA_1LD1RB_------_------; entry 7, period 5. -/
def p437 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert437 : zipCycle p437 7 5 false (1) = true := by decide +kernel
theorem never437 (m : Machine) (hm : compatible p437 m) : NeverHalts m :=
  zipCycle_sound p437 7 5 false (1) (by decide) cert437 m hm
#print axioms never437


/-- Third-level first-hole refinement 438, 1RB0LC_1RC1LB_0RD1LA_1LD1RB_------_------; entry 13, period 1. -/
def p438 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert438 : zipCycle p438 13 1 false (-1) = true := by decide +kernel
theorem never438 (m : Machine) (hm : compatible p438 m) : NeverHalts m :=
  zipCycle_sound p438 13 1 false (-1) (by decide) cert438 m hm
#print axioms never438


/-- Third-level first-hole refinement 439, 1RB1LC_1RC1LB_0RD1LA_1LD1RB_------_------; entry 7, period 7. -/
def p439 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert439 : zipCycle p439 7 7 false (1) = true := by decide +kernel
theorem never439 (m : Machine) (hm : compatible p439 m) : NeverHalts m :=
  zipCycle_sound p439 7 7 false (1) (by decide) cert439 m hm
#print axioms never439


/-- Third-level first-hole refinement 440, 1RB0RC_1RC1LB_0RD1LA_1LD1RB_------_------; entry 7, period 7. -/
def p440 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert440 : zipCycle p440 7 7 false (1) = true := by decide +kernel
theorem never440 (m : Machine) (hm : compatible p440 m) : NeverHalts m :=
  zipCycle_sound p440 7 7 false (1) (by decide) cert440 m hm
#print axioms never440


/-- Third-level first-hole refinement 441, 1RB1RC_1RC1LB_0RD1LA_1LD1RB_------_------; entry 10, period 2. -/
def p441 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert441 : zipCycle p441 10 2 true (-1) = true := by decide +kernel
theorem never441 (m : Machine) (hm : compatible p441 m) : NeverHalts m :=
  zipCycle_sound p441 10 2 true (-1) (by decide) cert441 m hm
#print axioms never441


/-- Third-level first-hole refinement 442, 1RB0LD_1RC1LB_0RD1LA_1LD1RB_------_------; entry 12, period 1. -/
def p442 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert442 : zipCycle p442 12 1 false (-2) = true := by decide +kernel
theorem never442 (m : Machine) (hm : compatible p442 m) : NeverHalts m :=
  zipCycle_sound p442 12 1 false (-2) (by decide) cert442 m hm
#print axioms never442


/-- Third-level first-hole refinement 443, 1RB1LD_1RC1LB_0RD1LA_1LD1RB_------_------; entry 12, period 1. -/
def p443 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert443 : zipCycle p443 12 1 false (-2) = true := by decide +kernel
theorem never443 (m : Machine) (hm : compatible p443 m) : NeverHalts m :=
  zipCycle_sound p443 12 1 false (-2) (by decide) cert443 m hm
#print axioms never443


/-- Third-level first-hole refinement 444, 1RB0RD_1RC1LB_0RD1LA_1LD1RB_------_------; entry 7, period 6. -/
def p444 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert444 : zipCycle p444 7 6 true (-1) = true := by decide +kernel
theorem never444 (m : Machine) (hm : compatible p444 m) : NeverHalts m :=
  zipCycle_sound p444 7 6 true (-1) (by decide) cert444 m hm
#print axioms never444


/-- Third-level first-hole refinement 445, 1RB1RD_1RC1LB_0RD1LA_1LD1RB_------_------; entry 5, period 7. -/
def p445 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert445 : zipCycle p445 5 7 false (2) = true := by decide +kernel
theorem never445 (m : Machine) (hm : compatible p445 m) : NeverHalts m :=
  zipCycle_sound p445 5 7 false (2) (by decide) cert445 m hm
#print axioms never445


/-- Third-level first-hole refinement 446, 1RB1LA_1RC1LB_0RD0RA_1LD1RB_------_------; entry 6, period 7. -/
def p446 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert446 : zipCycle p446 6 7 false (2) = true := by decide +kernel
theorem never446 (m : Machine) (hm : compatible p446 m) : NeverHalts m :=
  zipCycle_sound p446 6 7 false (2) (by decide) cert446 m hm
#print axioms never446


/-- Third-level first-hole refinement 447, 1RB0RA_1RC1LB_0RD0RA_1LD1RB_------_------; entry 0, period 14. -/
def p447 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert447 : zipCycle p447 0 14 true (-1) = true := by decide +kernel
theorem never447 (m : Machine) (hm : compatible p447 m) : NeverHalts m :=
  zipCycle_sound p447 0 14 true (-1) (by decide) cert447 m hm
#print axioms never447


/-- Third-level first-hole refinement 448, 1RB1LB_1RC1LB_0RD0RA_1LD1RB_------_------; entry 0, period 20. -/
def p448 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert448 : zipCycle p448 0 20 true (-1) = true := by decide +kernel
theorem never448 (m : Machine) (hm : compatible p448 m) : NeverHalts m :=
  zipCycle_sound p448 0 20 true (-1) (by decide) cert448 m hm
#print axioms never448


/-- Third-level first-hole refinement 449, 1RB0RB_1RC1LB_0RD0RA_1LD1RB_------_------; entry 0, period 29. -/
def p449 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert449 : zipCycle p449 0 29 true (-1) = true := by decide +kernel
theorem never449 (m : Machine) (hm : compatible p449 m) : NeverHalts m :=
  zipCycle_sound p449 0 29 true (-1) (by decide) cert449 m hm
#print axioms never449


/-- Third-level first-hole refinement 450, 1RB1RB_1RC1LB_0RD0RA_1LD1RB_------_------; entry 1, period 21. -/
def p450 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert450 : zipCycle p450 1 21 true (-1) = true := by decide +kernel
theorem never450 (m : Machine) (hm : compatible p450 m) : NeverHalts m :=
  zipCycle_sound p450 1 21 true (-1) (by decide) cert450 m hm
#print axioms never450


/-- Third-level first-hole refinement 451, 1RB0LC_1RC1LB_0RD0RA_1LD1RB_------_------; entry 7, period 9. -/
def p451 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert451 : zipCycle p451 7 9 false (1) = true := by decide +kernel
theorem never451 (m : Machine) (hm : compatible p451 m) : NeverHalts m :=
  zipCycle_sound p451 7 9 false (1) (by decide) cert451 m hm
#print axioms never451


/-- Third-level first-hole refinement 452, 1RB1LC_1RC1LB_0RD0RA_1LD1RB_------_------; entry 1, period 27. -/
def p452 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert452 : zipCycle p452 1 27 true (-1) = true := by decide +kernel
theorem never452 (m : Machine) (hm : compatible p452 m) : NeverHalts m :=
  zipCycle_sound p452 1 27 true (-1) (by decide) cert452 m hm
#print axioms never452


/-- Third-level first-hole refinement 453, 1RB0RC_1RC1LB_0RD0RA_1LD1RB_------_------; entry 0, period 32. -/
def p453 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert453 : zipCycle p453 0 32 true (-2) = true := by decide +kernel
theorem never453 (m : Machine) (hm : compatible p453 m) : NeverHalts m :=
  zipCycle_sound p453 0 32 true (-2) (by decide) cert453 m hm
#print axioms never453


/-- Third-level first-hole refinement 454, 1RB1RC_1RC1LB_0RD0RA_1LD1RB_------_------; entry 0, period 24. -/
def p454 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert454 : zipCycle p454 0 24 true (-1) = true := by decide +kernel
theorem never454 (m : Machine) (hm : compatible p454 m) : NeverHalts m :=
  zipCycle_sound p454 0 24 true (-1) (by decide) cert454 m hm
#print axioms never454


/-- Third-level first-hole refinement 455, 1RB0LD_1RC1LB_0RD0RA_1LD1RB_------_------; entry 7, period 7. -/
def p455 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert455 : zipCycle p455 7 7 false (1) = true := by decide +kernel
theorem never455 (m : Machine) (hm : compatible p455 m) : NeverHalts m :=
  zipCycle_sound p455 7 7 false (1) (by decide) cert455 m hm
#print axioms never455


/-- Third-level first-hole refinement 456, 1RB1LD_1RC1LB_0RD0RA_1LD1RB_------_------; entry 7, period 7. -/
def p456 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert456 : zipCycle p456 7 7 false (1) = true := by decide +kernel
theorem never456 (m : Machine) (hm : compatible p456 m) : NeverHalts m :=
  zipCycle_sound p456 7 7 false (1) (by decide) cert456 m hm
#print axioms never456


/-- Third-level first-hole refinement 457, 1RB0RD_1RC1LB_0RD0RA_1LD1RB_------_------; entry 7, period 15. -/
def p457 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert457 : zipCycle p457 7 15 true (-1) = true := by decide +kernel
theorem never457 (m : Machine) (hm : compatible p457 m) : NeverHalts m :=
  zipCycle_sound p457 7 15 true (-1) (by decide) cert457 m hm
#print axioms never457


/-- Third-level first-hole refinement 458, 1RB1RD_1RC1LB_0RD0RA_1LD1RB_------_------; entry 5, period 27. -/
def p458 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert458 : zipCycle p458 5 27 true (-1) = true := by decide +kernel
theorem never458 (m : Machine) (hm : compatible p458 m) : NeverHalts m :=
  zipCycle_sound p458 5 27 true (-1) (by decide) cert458 m hm
#print axioms never458


/-- Third-level first-hole refinement 459, 1RB0LA_1RC1LB_0RD1RA_1LD1RB_------_------; entry 0, period 14. -/
def p459 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert459 : zipCycle p459 0 14 false (3) = true := by decide +kernel
theorem never459 (m : Machine) (hm : compatible p459 m) : NeverHalts m :=
  zipCycle_sound p459 0 14 false (3) (by decide) cert459 m hm
#print axioms never459


/-- Third-level first-hole refinement 460, 1RB1LA_1RC1LB_0RD1RA_1LD1RB_------_------; entry 7, period 8. -/
def p460 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert460 : zipCycle p460 7 8 false (1) = true := by decide +kernel
theorem never460 (m : Machine) (hm : compatible p460 m) : NeverHalts m :=
  zipCycle_sound p460 7 8 false (1) (by decide) cert460 m hm
#print axioms never460


/-- Third-level first-hole refinement 461, 1RB0RA_1RC1LB_0RD1RA_1LD1RB_------_------; entry 0, period 14. -/
def p461 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert461 : zipCycle p461 0 14 true (-1) = true := by decide +kernel
theorem never461 (m : Machine) (hm : compatible p461 m) : NeverHalts m :=
  zipCycle_sound p461 0 14 true (-1) (by decide) cert461 m hm
#print axioms never461


/-- Third-level first-hole refinement 462, 1RB0LB_1RC1LB_0RD1RA_1LD1RB_------_------; entry 7, period 5. -/
def p462 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert462 : zipCycle p462 7 5 false (1) = true := by decide +kernel
theorem never462 (m : Machine) (hm : compatible p462 m) : NeverHalts m :=
  zipCycle_sound p462 7 5 false (1) (by decide) cert462 m hm
#print axioms never462


/-- Third-level first-hole refinement 463, 1RB1LB_1RC1LB_0RD1RA_1LD1RB_------_------; entry 7, period 5. -/
def p463 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert463 : zipCycle p463 7 5 false (1) = true := by decide +kernel
theorem never463 (m : Machine) (hm : compatible p463 m) : NeverHalts m :=
  zipCycle_sound p463 7 5 false (1) (by decide) cert463 m hm
#print axioms never463


/-- Third-level first-hole refinement 464, 1RB1RB_1RC1LB_0RD1RA_1LD1RB_------_------; entry 6, period 7. -/
def p464 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert464 : zipCycle p464 6 7 false (2) = true := by decide +kernel
theorem never464 (m : Machine) (hm : compatible p464 m) : NeverHalts m :=
  zipCycle_sound p464 6 7 false (2) (by decide) cert464 m hm
#print axioms never464


/-- Third-level first-hole refinement 465, 1RB0LC_1RC1LB_0RD1RA_1LD1RB_------_------; entry 6, period 9. -/
def p465 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert465 : zipCycle p465 6 9 false (2) = true := by decide +kernel
theorem never465 (m : Machine) (hm : compatible p465 m) : NeverHalts m :=
  zipCycle_sound p465 6 9 false (2) (by decide) cert465 m hm
#print axioms never465


/-- Third-level first-hole refinement 466, 1RB1LC_1RC1LB_0RD1RA_1LD1RB_------_------; entry 10, period 2. -/
def p466 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert466 : zipCycle p466 10 2 true (0) = true := by decide +kernel
theorem never466 (m : Machine) (hm : compatible p466 m) : NeverHalts m :=
  zipCycle_sound p466 10 2 true (0) (by decide) cert466 m hm
#print axioms never466


/-- Third-level first-hole refinement 467, 1RB0RC_1RC1LB_0RD1RA_1LD1RB_------_------; entry 7, period 12. -/
def p467 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert467 : zipCycle p467 7 12 true (-1) = true := by decide +kernel
theorem never467 (m : Machine) (hm : compatible p467 m) : NeverHalts m :=
  zipCycle_sound p467 7 12 true (-1) (by decide) cert467 m hm
#print axioms never467


/-- Third-level first-hole refinement 468, 1RB1LD_1RC1LB_0RD1RA_1LD1RB_------_------; entry 5, period 7. -/
def p468 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert468 : zipCycle p468 5 7 false (2) = true := by decide +kernel
theorem never468 (m : Machine) (hm : compatible p468 m) : NeverHalts m :=
  zipCycle_sound p468 5 7 false (2) (by decide) cert468 m hm
#print axioms never468


/-- Third-level first-hole refinement 469, 1RB1RD_1RC1LB_0RD1RA_1LD1RB_------_------; entry 6, period 9. -/
def p469 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert469 : zipCycle p469 6 9 false (3) = true := by decide +kernel
theorem never469 (m : Machine) (hm : compatible p469 m) : NeverHalts m :=
  zipCycle_sound p469 6 9 false (3) (by decide) cert469 m hm
#print axioms never469


/-- Third-level first-hole refinement 470, 1RB---_1RC1LB_0RD0LE_1LD1RB_---1LA_------; entry 7, period 6. -/
def p470 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert470 : zipCycle p470 7 6 false (1) = true := by decide +kernel
theorem never470 (m : Machine) (hm : compatible p470 m) : NeverHalts m :=
  zipCycle_sound p470 7 6 false (1) (by decide) cert470 m hm
#print axioms never470


/-- Third-level first-hole refinement 471, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0RA_------; entry 7, period 6. -/
def p471 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert471 : zipCycle p471 7 6 true (-1) = true := by decide +kernel
theorem never471 (m : Machine) (hm : compatible p471 m) : NeverHalts m :=
  zipCycle_sound p471 7 6 true (-1) (by decide) cert471 m hm
#print axioms never471


/-- Third-level first-hole refinement 472, 1RB---_1RC1LB_0RD0LE_1LD1RB_---1RA_------; entry 6, period 7. -/
def p472 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert472 : zipCycle p472 6 7 false (2) = true := by decide +kernel
theorem never472 (m : Machine) (hm : compatible p472 m) : NeverHalts m :=
  zipCycle_sound p472 6 7 false (2) (by decide) cert472 m hm
#print axioms never472


/-- Third-level first-hole refinement 473, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0LB_------; entry 7, period 10. -/
def p473 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert473 : zipCycle p473 7 10 false (1) = true := by decide +kernel
theorem never473 (m : Machine) (hm : compatible p473 m) : NeverHalts m :=
  zipCycle_sound p473 7 10 false (1) (by decide) cert473 m hm
#print axioms never473


/-- Third-level first-hole refinement 474, 1RB---_1RC1LB_0RD0LE_1LD1RB_---1LB_------; entry 9, period 3. -/
def p474 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert474 : zipCycle p474 9 3 false (0) = true := by decide +kernel
theorem never474 (m : Machine) (hm : compatible p474 m) : NeverHalts m :=
  zipCycle_sound p474 9 3 false (0) (by decide) cert474 m hm
#print axioms never474


/-- Third-level first-hole refinement 475, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0RB_------; entry 12, period 16. -/
def p475 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert475 : zipCycle p475 12 16 true (0) = true := by decide +kernel
theorem never475 (m : Machine) (hm : compatible p475 m) : NeverHalts m :=
  zipCycle_sound p475 12 16 true (0) (by decide) cert475 m hm
#print axioms never475


/-- Third-level first-hole refinement 476, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0LC_------; entry 13, period 1. -/
def p476 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert476 : zipCycle p476 13 1 false (-1) = true := by decide +kernel
theorem never476 (m : Machine) (hm : compatible p476 m) : NeverHalts m :=
  zipCycle_sound p476 13 1 false (-1) (by decide) cert476 m hm
#print axioms never476


/-- Third-level first-hole refinement 477, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0RC_------; entry 1, period 27. -/
def p477 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert477 : zipCycle p477 1 27 true (-1) = true := by decide +kernel
theorem never477 (m : Machine) (hm : compatible p477 m) : NeverHalts m :=
  zipCycle_sound p477 1 27 true (-1) (by decide) cert477 m hm
#print axioms never477


/-- Third-level first-hole refinement 478, 1RB---_1RC1LB_0RD0LE_1LD1RB_---1RC_------; entry 1, period 27. -/
def p478 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert478 : zipCycle p478 1 27 true (-1) = true := by decide +kernel
theorem never478 (m : Machine) (hm : compatible p478 m) : NeverHalts m :=
  zipCycle_sound p478 1 27 true (-1) (by decide) cert478 m hm
#print axioms never478


/-- Third-level first-hole refinement 479, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0LD_------; entry 12, period 1. -/
def p479 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert479 : zipCycle p479 12 1 false (-2) = true := by decide +kernel
theorem never479 (m : Machine) (hm : compatible p479 m) : NeverHalts m :=
  zipCycle_sound p479 12 1 false (-2) (by decide) cert479 m hm
#print axioms never479


/-- Third-level first-hole refinement 480, 1RB---_1RC1LB_0RD0LE_1LD1RB_---1LD_------; entry 12, period 1. -/
def p480 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert480 : zipCycle p480 12 1 false (-2) = true := by decide +kernel
theorem never480 (m : Machine) (hm : compatible p480 m) : NeverHalts m :=
  zipCycle_sound p480 12 1 false (-2) (by decide) cert480 m hm
#print axioms never480


/-- Third-level first-hole refinement 481, 1RB---_1RC1LB_0RD0LE_1LD1RB_---0RD_------; entry 12, period 1. -/
def p481 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert481 : zipCycle p481 12 1 false (0) = true := by decide +kernel
theorem never481 (m : Machine) (hm : compatible p481 m) : NeverHalts m :=
  zipCycle_sound p481 12 1 false (0) (by decide) cert481 m hm
#print axioms never481


/-- Third-level first-hole refinement 482, 1RB---_1RC1LB_0RD0LE_1LD1RB_---1RD_------; entry 7, period 7. -/
def p482 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert482 : zipCycle p482 7 7 false (1) = true := by decide +kernel
theorem never482 (m : Machine) (hm : compatible p482 m) : NeverHalts m :=
  zipCycle_sound p482 7 7 false (1) (by decide) cert482 m hm
#print axioms never482


/-- Third-level first-hole refinement 483, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1LA_------; entry 7, period 6. -/
def p483 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert483 : zipCycle p483 7 6 false (1) = true := by decide +kernel
theorem never483 (m : Machine) (hm : compatible p483 m) : NeverHalts m :=
  zipCycle_sound p483 7 6 false (1) (by decide) cert483 m hm
#print axioms never483


/-- Third-level first-hole refinement 484, 1RB---_1RC1LB_0RD1LE_1LD1RB_---0LB_------; entry 16, period 14. -/
def p484 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert484 : zipCycle p484 16 14 false (0) = true := by decide +kernel
theorem never484 (m : Machine) (hm : compatible p484 m) : NeverHalts m :=
  zipCycle_sound p484 16 14 false (0) (by decide) cert484 m hm
#print axioms never484


/-- Third-level first-hole refinement 485, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1LB_------; entry 9, period 3. -/
def p485 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert485 : zipCycle p485 9 3 false (0) = true := by decide +kernel
theorem never485 (m : Machine) (hm : compatible p485 m) : NeverHalts m :=
  zipCycle_sound p485 9 3 false (0) (by decide) cert485 m hm
#print axioms never485


/-- Third-level first-hole refinement 486, 1RB---_1RC1LB_0RD1LE_1LD1RB_---0RB_------; entry 8, period 4. -/
def p486 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert486 : zipCycle p486 8 4 true (-1) = true := by decide +kernel
theorem never486 (m : Machine) (hm : compatible p486 m) : NeverHalts m :=
  zipCycle_sound p486 8 4 true (-1) (by decide) cert486 m hm
#print axioms never486


/-- Third-level first-hole refinement 487, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1RB_------; entry 7, period 5. -/
def p487 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert487 : zipCycle p487 7 5 false (1) = true := by decide +kernel
theorem never487 (m : Machine) (hm : compatible p487 m) : NeverHalts m :=
  zipCycle_sound p487 7 5 false (1) (by decide) cert487 m hm
#print axioms never487


/-- Third-level first-hole refinement 488, 1RB---_1RC1LB_0RD1LE_1LD1RB_---0LC_------; entry 13, period 1. -/
def p488 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert488 : zipCycle p488 13 1 false (-1) = true := by decide +kernel
theorem never488 (m : Machine) (hm : compatible p488 m) : NeverHalts m :=
  zipCycle_sound p488 13 1 false (-1) (by decide) cert488 m hm
#print axioms never488


/-- Third-level first-hole refinement 489, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1LC_------; entry 7, period 7. -/
def p489 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert489 : zipCycle p489 7 7 false (1) = true := by decide +kernel
theorem never489 (m : Machine) (hm : compatible p489 m) : NeverHalts m :=
  zipCycle_sound p489 7 7 false (1) (by decide) cert489 m hm
#print axioms never489


/-- Third-level first-hole refinement 490, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1RC_------; entry 10, period 2. -/
def p490 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert490 : zipCycle p490 10 2 true (-1) = true := by decide +kernel
theorem never490 (m : Machine) (hm : compatible p490 m) : NeverHalts m :=
  zipCycle_sound p490 10 2 true (-1) (by decide) cert490 m hm
#print axioms never490


/-- Third-level first-hole refinement 491, 1RB---_1RC1LB_0RD1LE_1LD1RB_---0LD_------; entry 12, period 1. -/
def p491 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert491 : zipCycle p491 12 1 false (-2) = true := by decide +kernel
theorem never491 (m : Machine) (hm : compatible p491 m) : NeverHalts m :=
  zipCycle_sound p491 12 1 false (-2) (by decide) cert491 m hm
#print axioms never491


/-- Third-level first-hole refinement 492, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1LD_------; entry 12, period 1. -/
def p492 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert492 : zipCycle p492 12 1 false (-2) = true := by decide +kernel
theorem never492 (m : Machine) (hm : compatible p492 m) : NeverHalts m :=
  zipCycle_sound p492 12 1 false (-2) (by decide) cert492 m hm
#print axioms never492


/-- Third-level first-hole refinement 493, 1RB---_1RC1LB_0RD1LE_1LD1RB_---0RD_------; entry 7, period 6. -/
def p493 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert493 : zipCycle p493 7 6 true (-1) = true := by decide +kernel
theorem never493 (m : Machine) (hm : compatible p493 m) : NeverHalts m :=
  zipCycle_sound p493 7 6 true (-1) (by decide) cert493 m hm
#print axioms never493


/-- Third-level first-hole refinement 494, 1RB---_1RC1LB_0RD1LE_1LD1RB_---1RD_------; entry 5, period 7. -/
def p494 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert494 : zipCycle p494 5 7 false (2) = true := by decide +kernel
theorem never494 (m : Machine) (hm : compatible p494 m) : NeverHalts m :=
  zipCycle_sound p494 5 7 false (2) (by decide) cert494 m hm
#print axioms never494


/-- Third-level first-hole refinement 495, 1RB---_1RC1LB_0RD0RE_1LD1RB_---1LA_------; entry 6, period 7. -/
def p495 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert495 : zipCycle p495 6 7 false (2) = true := by decide +kernel
theorem never495 (m : Machine) (hm : compatible p495 m) : NeverHalts m :=
  zipCycle_sound p495 6 7 false (2) (by decide) cert495 m hm
#print axioms never495


/-- Third-level first-hole refinement 496, 1RB---_1RC1LB_0RD0RE_1LD1RB_---1RB_------; entry 1, period 21. -/
def p496 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert496 : zipCycle p496 1 21 true (-1) = true := by decide +kernel
theorem never496 (m : Machine) (hm : compatible p496 m) : NeverHalts m :=
  zipCycle_sound p496 1 21 true (-1) (by decide) cert496 m hm
#print axioms never496


/-- Third-level first-hole refinement 497, 1RB---_1RC1LB_0RD0RE_1LD1RB_---0LC_------; entry 7, period 9. -/
def p497 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert497 : zipCycle p497 7 9 false (1) = true := by decide +kernel
theorem never497 (m : Machine) (hm : compatible p497 m) : NeverHalts m :=
  zipCycle_sound p497 7 9 false (1) (by decide) cert497 m hm
#print axioms never497


/-- Third-level first-hole refinement 498, 1RB---_1RC1LB_0RD0RE_1LD1RB_---1LC_------; entry 1, period 27. -/
def p498 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert498 : zipCycle p498 1 27 true (-1) = true := by decide +kernel
theorem never498 (m : Machine) (hm : compatible p498 m) : NeverHalts m :=
  zipCycle_sound p498 1 27 true (-1) (by decide) cert498 m hm
#print axioms never498


/-- Third-level first-hole refinement 499, 1RB---_1RC1LB_0RD0RE_1LD1RB_---0LD_------; entry 7, period 7. -/
def p499 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert499 : zipCycle p499 7 7 false (1) = true := by decide +kernel
theorem never499 (m : Machine) (hm : compatible p499 m) : NeverHalts m :=
  zipCycle_sound p499 7 7 false (1) (by decide) cert499 m hm
#print axioms never499

end BB6.Agent24Raw45D3_04
