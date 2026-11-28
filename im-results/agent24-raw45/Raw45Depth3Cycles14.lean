import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_14
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1400, 1RB---_1RC0RE_0RD---_1LD1RB_1LB1RE_------; entry 6, period 3. -/
def p1400 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1400 : zipCycle p1400 6 3 true (2) = true := by decide +kernel
theorem never1400 (m : Machine) (hm : compatible p1400 m) : NeverHalts m :=
  zipCycle_sound p1400 6 3 true (2) (by decide) cert1400 m hm
#print axioms never1400


/-- Third-level first-hole refinement 1401, 1RB---_1RC0RE_0RD---_1LD1RB_0RB1RE_------; entry 1, period 8. -/
def p1401 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1401 : zipCycle p1401 1 8 true (1) = true := by decide +kernel
theorem never1401 (m : Machine) (hm : compatible p1401 m) : NeverHalts m :=
  zipCycle_sound p1401 1 8 true (1) (by decide) cert1401 m hm
#print axioms never1401


/-- Third-level first-hole refinement 1402, 1RB---_1RC0RE_0RD---_1LD1RB_1RB1RE_------; entry 1, period 8. -/
def p1402 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1402 : zipCycle p1402 1 8 true (1) = true := by decide +kernel
theorem never1402 (m : Machine) (hm : compatible p1402 m) : NeverHalts m :=
  zipCycle_sound p1402 1 8 true (1) (by decide) cert1402 m hm
#print axioms never1402


/-- Third-level first-hole refinement 1403, 1RB---_1RC0RE_0RD---_1LD1RB_0RC1RE_------; entry 7, period 9. -/
def p1403 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1403 : zipCycle p1403 7 9 true (3) = true := by decide +kernel
theorem never1403 (m : Machine) (hm : compatible p1403 m) : NeverHalts m :=
  zipCycle_sound p1403 7 9 true (3) (by decide) cert1403 m hm
#print axioms never1403


/-- Third-level first-hole refinement 1404, 1RB---_1RC0RE_0RD---_1LD1RB_1RC1RE_------; entry 2, period 7. -/
def p1404 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1404 : zipCycle p1404 2 7 true (1) = true := by decide +kernel
theorem never1404 (m : Machine) (hm : compatible p1404 m) : NeverHalts m :=
  zipCycle_sound p1404 2 7 true (1) (by decide) cert1404 m hm
#print axioms never1404


/-- Third-level first-hole refinement 1405, 1RB---_1RC0RE_0RD---_1LD1RB_0LD1RE_------; entry 1, period 9. -/
def p1405 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1405 : zipCycle p1405 1 9 true (1) = true := by decide +kernel
theorem never1405 (m : Machine) (hm : compatible p1405 m) : NeverHalts m :=
  zipCycle_sound p1405 1 9 true (1) (by decide) cert1405 m hm
#print axioms never1405


/-- Third-level first-hole refinement 1406, 1RB---_1RC0RE_0RD---_1LD1RB_1LD1RE_------; entry 4, period 8. -/
def p1406 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1406 : zipCycle p1406 4 8 true (1) = true := by decide +kernel
theorem never1406 (m : Machine) (hm : compatible p1406 m) : NeverHalts m :=
  zipCycle_sound p1406 4 8 true (1) (by decide) cert1406 m hm
#print axioms never1406


/-- Third-level first-hole refinement 1407, 1RB---_1RC0RE_0RD---_1LD1RB_0RD1RE_------; entry 3, period 6. -/
def p1407 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1407 : zipCycle p1407 3 6 true (1) = true := by decide +kernel
theorem never1407 (m : Machine) (hm : compatible p1407 m) : NeverHalts m :=
  zipCycle_sound p1407 3 6 true (1) (by decide) cert1407 m hm
#print axioms never1407


/-- Third-level first-hole refinement 1408, 1RB---_1RC0RE_0RD---_1LD1RB_1RD1RE_------; entry 8, period 4. -/
def p1408 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1408 : zipCycle p1408 8 4 true (4) = true := by decide +kernel
theorem never1408 (m : Machine) (hm : compatible p1408 m) : NeverHalts m :=
  zipCycle_sound p1408 8 4 true (4) (by decide) cert1408 m hm
#print axioms never1408


/-- Third-level first-hole refinement 1409, 1RB---_1RC0RE_0RD---_1LD1RB_0LE1RE_------; entry 7, period 2. -/
def p1409 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1409 : zipCycle p1409 7 2 true (3) = true := by decide +kernel
theorem never1409 (m : Machine) (hm : compatible p1409 m) : NeverHalts m :=
  zipCycle_sound p1409 7 2 true (3) (by decide) cert1409 m hm
#print axioms never1409


/-- Third-level first-hole refinement 1410, 1RB---_1RC0RE_0RD---_1LD1RB_1LE1RE_------; entry 7, period 3. -/
def p1410 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1410 : zipCycle p1410 7 3 true (3) = true := by decide +kernel
theorem never1410 (m : Machine) (hm : compatible p1410 m) : NeverHalts m :=
  zipCycle_sound p1410 7 3 true (3) (by decide) cert1410 m hm
#print axioms never1410


/-- Third-level first-hole refinement 1411, 1RB---_1RC0RE_0RD---_1LD1RB_0RE1RE_------; entry 8, period 1. -/
def p1411 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1411 : zipCycle p1411 8 1 true (4) = true := by decide +kernel
theorem never1411 (m : Machine) (hm : compatible p1411 m) : NeverHalts m :=
  zipCycle_sound p1411 8 1 true (4) (by decide) cert1411 m hm
#print axioms never1411


/-- Third-level first-hole refinement 1412, 1RB---_1RC0RE_0RD---_1LD1RB_1RE1RE_------; entry 8, period 1. -/
def p1412 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1412 : zipCycle p1412 8 1 true (4) = true := by decide +kernel
theorem never1412 (m : Machine) (hm : compatible p1412 m) : NeverHalts m :=
  zipCycle_sound p1412 8 1 true (4) (by decide) cert1412 m hm
#print axioms never1412


/-- Third-level first-hole refinement 1413, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_0RA---; entry 0, period 9. -/
def p1413 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1413 : zipCycle p1413 0 9 true (0) = true := by decide +kernel
theorem never1413 (m : Machine) (hm : compatible p1413 m) : NeverHalts m :=
  zipCycle_sound p1413 0 9 true (0) (by decide) cert1413 m hm
#print axioms never1413


/-- Third-level first-hole refinement 1414, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_1RA---; entry 0, period 9. -/
def p1414 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1414 : zipCycle p1414 0 9 true (0) = true := by decide +kernel
theorem never1414 (m : Machine) (hm : compatible p1414 m) : NeverHalts m :=
  zipCycle_sound p1414 0 9 true (0) (by decide) cert1414 m hm
#print axioms never1414


/-- Third-level first-hole refinement 1415, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_0RB---; entry 1, period 8. -/
def p1415 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1415 : zipCycle p1415 1 8 true (1) = true := by decide +kernel
theorem never1415 (m : Machine) (hm : compatible p1415 m) : NeverHalts m :=
  zipCycle_sound p1415 1 8 true (1) (by decide) cert1415 m hm
#print axioms never1415


/-- Third-level first-hole refinement 1416, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_1RB---; entry 1, period 8. -/
def p1416 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1416 : zipCycle p1416 1 8 true (1) = true := by decide +kernel
theorem never1416 (m : Machine) (hm : compatible p1416 m) : NeverHalts m :=
  zipCycle_sound p1416 1 8 true (1) (by decide) cert1416 m hm
#print axioms never1416


/-- Third-level first-hole refinement 1417, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_0RC---; entry 1, period 18. -/
def p1417 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1417 : zipCycle p1417 1 18 true (1) = true := by decide +kernel
theorem never1417 (m : Machine) (hm : compatible p1417 m) : NeverHalts m :=
  zipCycle_sound p1417 1 18 true (1) (by decide) cert1417 m hm
#print axioms never1417


/-- Third-level first-hole refinement 1418, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_1RC---; entry 2, period 7. -/
def p1418 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1418 : zipCycle p1418 2 7 true (1) = true := by decide +kernel
theorem never1418 (m : Machine) (hm : compatible p1418 m) : NeverHalts m :=
  zipCycle_sound p1418 2 7 true (1) (by decide) cert1418 m hm
#print axioms never1418


/-- Third-level first-hole refinement 1419, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_0LD---; entry 1, period 9. -/
def p1419 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1419 : zipCycle p1419 1 9 true (1) = true := by decide +kernel
theorem never1419 (m : Machine) (hm : compatible p1419 m) : NeverHalts m :=
  zipCycle_sound p1419 1 9 true (1) (by decide) cert1419 m hm
#print axioms never1419


/-- Third-level first-hole refinement 1420, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_0RD---; entry 3, period 6. -/
def p1420 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1420 : zipCycle p1420 3 6 true (1) = true := by decide +kernel
theorem never1420 (m : Machine) (hm : compatible p1420 m) : NeverHalts m :=
  zipCycle_sound p1420 3 6 true (1) (by decide) cert1420 m hm
#print axioms never1420


/-- Third-level first-hole refinement 1421, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_0RF---; entry 8, period 1. -/
def p1421 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨false,true,5⟩)
  | _,_ => none
theorem cert1421 : zipCycle p1421 8 1 true (2) = true := by decide +kernel
theorem never1421 (m : Machine) (hm : compatible p1421 m) : NeverHalts m :=
  zipCycle_sound p1421 8 1 true (2) (by decide) cert1421 m hm
#print axioms never1421


/-- Third-level first-hole refinement 1422, 1RB---_1RC0RE_0RD---_1LD1RB_---0LF_1RF---; entry 8, period 1. -/
def p1422 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,5⟩)
  | 5, false => some (some ⟨true,true,5⟩)
  | _,_ => none
theorem cert1422 : zipCycle p1422 8 1 true (2) = true := by decide +kernel
theorem never1422 (m : Machine) (hm : compatible p1422 m) : NeverHalts m :=
  zipCycle_sound p1422 8 1 true (2) (by decide) cert1422 m hm
#print axioms never1422


/-- Third-level first-hole refinement 1423, 1RB---_1RC0RE_0RD---_1LD1RB_---1LF_1LD---; entry 5, period 4. -/
def p1423 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert1423 : zipCycle p1423 5 4 true (1) = true := by decide +kernel
theorem never1423 (m : Machine) (hm : compatible p1423 m) : NeverHalts m :=
  zipCycle_sound p1423 5 4 true (1) (by decide) cert1423 m hm
#print axioms never1423


/-- Third-level first-hole refinement 1424, 1RB---_1RC0RE_0RD---_1LD1RB_---1LF_0RD---; entry 1, period 9. -/
def p1424 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1424 : zipCycle p1424 1 9 true (1) = true := by decide +kernel
theorem never1424 (m : Machine) (hm : compatible p1424 m) : NeverHalts m :=
  zipCycle_sound p1424 1 9 true (1) (by decide) cert1424 m hm
#print axioms never1424


/-- Third-level first-hole refinement 1425, 1RB---_1RC0RE_0RD---_1LD1RB_---1LF_1RD---; entry 1, period 9. -/
def p1425 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1425 : zipCycle p1425 1 9 true (1) = true := by decide +kernel
theorem never1425 (m : Machine) (hm : compatible p1425 m) : NeverHalts m :=
  zipCycle_sound p1425 1 9 true (1) (by decide) cert1425 m hm
#print axioms never1425


/-- Third-level first-hole refinement 1426, 1RB---_1RC0RE_0RD---_1LD1RB_---1LF_0RE---; entry 7, period 2. -/
def p1426 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,5⟩)
  | 5, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1426 : zipCycle p1426 7 2 true (2) = true := by decide +kernel
theorem never1426 (m : Machine) (hm : compatible p1426 m) : NeverHalts m :=
  zipCycle_sound p1426 7 2 true (2) (by decide) cert1426 m hm
#print axioms never1426


/-- Third-level first-hole refinement 1427, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_0LA---; entry 0, period 9. -/
def p1427 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1427 : zipCycle p1427 0 9 true (0) = true := by decide +kernel
theorem never1427 (m : Machine) (hm : compatible p1427 m) : NeverHalts m :=
  zipCycle_sound p1427 0 9 true (0) (by decide) cert1427 m hm
#print axioms never1427


/-- Third-level first-hole refinement 1428, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_0RA---; entry 0, period 9. -/
def p1428 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1428 : zipCycle p1428 0 9 true (0) = true := by decide +kernel
theorem never1428 (m : Machine) (hm : compatible p1428 m) : NeverHalts m :=
  zipCycle_sound p1428 0 9 true (0) (by decide) cert1428 m hm
#print axioms never1428


/-- Third-level first-hole refinement 1429, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_1RA---; entry 0, period 9. -/
def p1429 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1429 : zipCycle p1429 0 9 true (0) = true := by decide +kernel
theorem never1429 (m : Machine) (hm : compatible p1429 m) : NeverHalts m :=
  zipCycle_sound p1429 0 9 true (0) (by decide) cert1429 m hm
#print axioms never1429


/-- Third-level first-hole refinement 1430, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_0LB---; entry 1, period 8. -/
def p1430 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1430 : zipCycle p1430 1 8 true (1) = true := by decide +kernel
theorem never1430 (m : Machine) (hm : compatible p1430 m) : NeverHalts m :=
  zipCycle_sound p1430 1 8 true (1) (by decide) cert1430 m hm
#print axioms never1430


/-- Third-level first-hole refinement 1431, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_0RB---; entry 1, period 8. -/
def p1431 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1431 : zipCycle p1431 1 8 true (1) = true := by decide +kernel
theorem never1431 (m : Machine) (hm : compatible p1431 m) : NeverHalts m :=
  zipCycle_sound p1431 1 8 true (1) (by decide) cert1431 m hm
#print axioms never1431


/-- Third-level first-hole refinement 1432, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_1RB---; entry 1, period 8. -/
def p1432 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1432 : zipCycle p1432 1 8 true (1) = true := by decide +kernel
theorem never1432 (m : Machine) (hm : compatible p1432 m) : NeverHalts m :=
  zipCycle_sound p1432 1 8 true (1) (by decide) cert1432 m hm
#print axioms never1432


/-- Third-level first-hole refinement 1433, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_1LC---; entry 1, period 10. -/
def p1433 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1433 : zipCycle p1433 1 10 true (1) = true := by decide +kernel
theorem never1433 (m : Machine) (hm : compatible p1433 m) : NeverHalts m :=
  zipCycle_sound p1433 1 10 true (1) (by decide) cert1433 m hm
#print axioms never1433


/-- Third-level first-hole refinement 1434, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_1RC---; entry 2, period 7. -/
def p1434 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1434 : zipCycle p1434 2 7 true (1) = true := by decide +kernel
theorem never1434 (m : Machine) (hm : compatible p1434 m) : NeverHalts m :=
  zipCycle_sound p1434 2 7 true (1) (by decide) cert1434 m hm
#print axioms never1434


/-- Third-level first-hole refinement 1435, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_0LD---; entry 3, period 6. -/
def p1435 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1435 : zipCycle p1435 3 6 true (1) = true := by decide +kernel
theorem never1435 (m : Machine) (hm : compatible p1435 m) : NeverHalts m :=
  zipCycle_sound p1435 3 6 true (1) (by decide) cert1435 m hm
#print axioms never1435


/-- Third-level first-hole refinement 1436, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_0RF---; entry 8, period 1. -/
def p1436 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨false,true,5⟩)
  | _,_ => none
theorem cert1436 : zipCycle p1436 8 1 true (4) = true := by decide +kernel
theorem never1436 (m : Machine) (hm : compatible p1436 m) : NeverHalts m :=
  zipCycle_sound p1436 8 1 true (4) (by decide) cert1436 m hm
#print axioms never1436


/-- Third-level first-hole refinement 1437, 1RB---_1RC0RE_0RD---_1LD1RB_---0RF_1RF---; entry 8, period 1. -/
def p1437 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,5⟩)
  | 5, false => some (some ⟨true,true,5⟩)
  | _,_ => none
theorem cert1437 : zipCycle p1437 8 1 true (4) = true := by decide +kernel
theorem never1437 (m : Machine) (hm : compatible p1437 m) : NeverHalts m :=
  zipCycle_sound p1437 8 1 true (4) (by decide) cert1437 m hm
#print axioms never1437


/-- Third-level first-hole refinement 1438, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_0RA---; entry 0, period 9. -/
def p1438 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert1438 : zipCycle p1438 0 9 true (0) = true := by decide +kernel
theorem never1438 (m : Machine) (hm : compatible p1438 m) : NeverHalts m :=
  zipCycle_sound p1438 0 9 true (0) (by decide) cert1438 m hm
#print axioms never1438


/-- Third-level first-hole refinement 1439, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_1RA---; entry 0, period 9. -/
def p1439 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert1439 : zipCycle p1439 0 9 true (0) = true := by decide +kernel
theorem never1439 (m : Machine) (hm : compatible p1439 m) : NeverHalts m :=
  zipCycle_sound p1439 0 9 true (0) (by decide) cert1439 m hm
#print axioms never1439


/-- Third-level first-hole refinement 1440, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_1LB---; entry 6, period 3. -/
def p1440 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1440 : zipCycle p1440 6 3 true (2) = true := by decide +kernel
theorem never1440 (m : Machine) (hm : compatible p1440 m) : NeverHalts m :=
  zipCycle_sound p1440 6 3 true (2) (by decide) cert1440 m hm
#print axioms never1440


/-- Third-level first-hole refinement 1441, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_0RB---; entry 1, period 8. -/
def p1441 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert1441 : zipCycle p1441 1 8 true (1) = true := by decide +kernel
theorem never1441 (m : Machine) (hm : compatible p1441 m) : NeverHalts m :=
  zipCycle_sound p1441 1 8 true (1) (by decide) cert1441 m hm
#print axioms never1441


/-- Third-level first-hole refinement 1442, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_1RB---; entry 1, period 8. -/
def p1442 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1442 : zipCycle p1442 1 8 true (1) = true := by decide +kernel
theorem never1442 (m : Machine) (hm : compatible p1442 m) : NeverHalts m :=
  zipCycle_sound p1442 1 8 true (1) (by decide) cert1442 m hm
#print axioms never1442


/-- Third-level first-hole refinement 1443, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_1RC---; entry 2, period 7. -/
def p1443 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert1443 : zipCycle p1443 2 7 true (1) = true := by decide +kernel
theorem never1443 (m : Machine) (hm : compatible p1443 m) : NeverHalts m :=
  zipCycle_sound p1443 2 7 true (1) (by decide) cert1443 m hm
#print axioms never1443


/-- Third-level first-hole refinement 1444, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_0LD---; entry 1, period 9. -/
def p1444 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1444 : zipCycle p1444 1 9 true (1) = true := by decide +kernel
theorem never1444 (m : Machine) (hm : compatible p1444 m) : NeverHalts m :=
  zipCycle_sound p1444 1 9 true (1) (by decide) cert1444 m hm
#print axioms never1444


/-- Third-level first-hole refinement 1445, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_0RD---; entry 3, period 6. -/
def p1445 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert1445 : zipCycle p1445 3 6 true (1) = true := by decide +kernel
theorem never1445 (m : Machine) (hm : compatible p1445 m) : NeverHalts m :=
  zipCycle_sound p1445 3 6 true (1) (by decide) cert1445 m hm
#print axioms never1445


/-- Third-level first-hole refinement 1446, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_0LE---; entry 7, period 2. -/
def p1446 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1446 : zipCycle p1446 7 2 true (3) = true := by decide +kernel
theorem never1446 (m : Machine) (hm : compatible p1446 m) : NeverHalts m :=
  zipCycle_sound p1446 7 2 true (3) (by decide) cert1446 m hm
#print axioms never1446


/-- Third-level first-hole refinement 1447, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_0RF---; entry 8, period 1. -/
def p1447 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨false,true,5⟩)
  | _,_ => none
theorem cert1447 : zipCycle p1447 8 1 true (4) = true := by decide +kernel
theorem never1447 (m : Machine) (hm : compatible p1447 m) : NeverHalts m :=
  zipCycle_sound p1447 8 1 true (4) (by decide) cert1447 m hm
#print axioms never1447


/-- Third-level first-hole refinement 1448, 1RB---_1RC0RE_0RD---_1LD1RB_---1RF_1RF---; entry 8, period 1. -/
def p1448 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,5⟩)
  | 5, false => some (some ⟨true,true,5⟩)
  | _,_ => none
theorem cert1448 : zipCycle p1448 8 1 true (4) = true := by decide +kernel
theorem never1448 (m : Machine) (hm : compatible p1448 m) : NeverHalts m :=
  zipCycle_sound p1448 8 1 true (4) (by decide) cert1448 m hm
#print axioms never1448


/-- Third-level first-hole refinement 1449, 1RB0LA_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 0, period 11. -/
def p1449 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1449 : zipCycle p1449 0 11 false (3) = true := by decide +kernel
theorem never1449 (m : Machine) (hm : compatible p1449 m) : NeverHalts m :=
  zipCycle_sound p1449 0 11 false (3) (by decide) cert1449 m hm
#print axioms never1449


/-- Third-level first-hole refinement 1450, 1RB1LA_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 9, period 5. -/
def p1450 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1450 : zipCycle p1450 9 5 false (1) = true := by decide +kernel
theorem never1450 (m : Machine) (hm : compatible p1450 m) : NeverHalts m :=
  zipCycle_sound p1450 9 5 false (1) (by decide) cert1450 m hm
#print axioms never1450


/-- Third-level first-hole refinement 1451, 1RB0RA_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 0, period 9. -/
def p1451 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1451 : zipCycle p1451 0 9 true (0) = true := by decide +kernel
theorem never1451 (m : Machine) (hm : compatible p1451 m) : NeverHalts m :=
  zipCycle_sound p1451 0 9 true (0) (by decide) cert1451 m hm
#print axioms never1451


/-- Third-level first-hole refinement 1452, 1RB1RA_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 0, period 9. -/
def p1452 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1452 : zipCycle p1452 0 9 true (0) = true := by decide +kernel
theorem never1452 (m : Machine) (hm : compatible p1452 m) : NeverHalts m :=
  zipCycle_sound p1452 0 9 true (0) (by decide) cert1452 m hm
#print axioms never1452


/-- Third-level first-hole refinement 1453, 1RB0RB_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 1, period 8. -/
def p1453 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1453 : zipCycle p1453 1 8 true (1) = true := by decide +kernel
theorem never1453 (m : Machine) (hm : compatible p1453 m) : NeverHalts m :=
  zipCycle_sound p1453 1 8 true (1) (by decide) cert1453 m hm
#print axioms never1453


/-- Third-level first-hole refinement 1454, 1RB1RB_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 1, period 8. -/
def p1454 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1454 : zipCycle p1454 1 8 true (1) = true := by decide +kernel
theorem never1454 (m : Machine) (hm : compatible p1454 m) : NeverHalts m :=
  zipCycle_sound p1454 1 8 true (1) (by decide) cert1454 m hm
#print axioms never1454


/-- Third-level first-hole refinement 1455, 1RB0RC_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 1, period 18. -/
def p1455 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1455 : zipCycle p1455 1 18 true (1) = true := by decide +kernel
theorem never1455 (m : Machine) (hm : compatible p1455 m) : NeverHalts m :=
  zipCycle_sound p1455 1 18 true (1) (by decide) cert1455 m hm
#print axioms never1455


/-- Third-level first-hole refinement 1456, 1RB1RC_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 2, period 7. -/
def p1456 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1456 : zipCycle p1456 2 7 true (1) = true := by decide +kernel
theorem never1456 (m : Machine) (hm : compatible p1456 m) : NeverHalts m :=
  zipCycle_sound p1456 2 7 true (1) (by decide) cert1456 m hm
#print axioms never1456


/-- Third-level first-hole refinement 1457, 1RB0LD_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 1, period 9. -/
def p1457 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1457 : zipCycle p1457 1 9 true (1) = true := by decide +kernel
theorem never1457 (m : Machine) (hm : compatible p1457 m) : NeverHalts m :=
  zipCycle_sound p1457 1 9 true (1) (by decide) cert1457 m hm
#print axioms never1457


/-- Third-level first-hole refinement 1458, 1RB0RD_1RC1RE_0RD---_1LD1RB_---0LA_------; entry 3, period 6. -/
def p1458 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert1458 : zipCycle p1458 3 6 true (1) = true := by decide +kernel
theorem never1458 (m : Machine) (hm : compatible p1458 m) : NeverHalts m :=
  zipCycle_sound p1458 3 6 true (1) (by decide) cert1458 m hm
#print axioms never1458


/-- Third-level first-hole refinement 1459, 1RB0LA_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 0, period 11. -/
def p1459 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1459 : zipCycle p1459 0 11 false (3) = true := by decide +kernel
theorem never1459 (m : Machine) (hm : compatible p1459 m) : NeverHalts m :=
  zipCycle_sound p1459 0 11 false (3) (by decide) cert1459 m hm
#print axioms never1459


/-- Third-level first-hole refinement 1460, 1RB1LA_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 9, period 5. -/
def p1460 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1460 : zipCycle p1460 9 5 false (1) = true := by decide +kernel
theorem never1460 (m : Machine) (hm : compatible p1460 m) : NeverHalts m :=
  zipCycle_sound p1460 9 5 false (1) (by decide) cert1460 m hm
#print axioms never1460


/-- Third-level first-hole refinement 1461, 1RB0RA_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 0, period 10. -/
def p1461 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1461 : zipCycle p1461 0 10 true (0) = true := by decide +kernel
theorem never1461 (m : Machine) (hm : compatible p1461 m) : NeverHalts m :=
  zipCycle_sound p1461 0 10 true (0) (by decide) cert1461 m hm
#print axioms never1461


/-- Third-level first-hole refinement 1462, 1RB1RA_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 0, period 10. -/
def p1462 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1462 : zipCycle p1462 0 10 true (0) = true := by decide +kernel
theorem never1462 (m : Machine) (hm : compatible p1462 m) : NeverHalts m :=
  zipCycle_sound p1462 0 10 true (0) (by decide) cert1462 m hm
#print axioms never1462


/-- Third-level first-hole refinement 1463, 1RB1LD_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 5, period 4. -/
def p1463 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1463 : zipCycle p1463 5 4 true (1) = true := by decide +kernel
theorem never1463 (m : Machine) (hm : compatible p1463 m) : NeverHalts m :=
  zipCycle_sound p1463 5 4 true (1) (by decide) cert1463 m hm
#print axioms never1463


/-- Third-level first-hole refinement 1464, 1RB0RD_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 1, period 9. -/
def p1464 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1464 : zipCycle p1464 1 9 true (1) = true := by decide +kernel
theorem never1464 (m : Machine) (hm : compatible p1464 m) : NeverHalts m :=
  zipCycle_sound p1464 1 9 true (1) (by decide) cert1464 m hm
#print axioms never1464


/-- Third-level first-hole refinement 1465, 1RB1RD_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 1, period 9. -/
def p1465 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1465 : zipCycle p1465 1 9 true (1) = true := by decide +kernel
theorem never1465 (m : Machine) (hm : compatible p1465 m) : NeverHalts m :=
  zipCycle_sound p1465 1 9 true (1) (by decide) cert1465 m hm
#print axioms never1465


/-- Third-level first-hole refinement 1466, 1RB1RE_1RC1RE_0RD---_1LD1RB_---1LA_------; entry 7, period 2. -/
def p1466 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1466 : zipCycle p1466 7 2 true (2) = true := by decide +kernel
theorem never1466 (m : Machine) (hm : compatible p1466 m) : NeverHalts m :=
  zipCycle_sound p1466 7 2 true (2) (by decide) cert1466 m hm
#print axioms never1466


/-- Third-level first-hole refinement 1467, 1RB---_1RC1RE_0RD---_1LD1RB_0RA0LB_------; entry 0, period 10. -/
def p1467 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1467 : zipCycle p1467 0 10 true (0) = true := by decide +kernel
theorem never1467 (m : Machine) (hm : compatible p1467 m) : NeverHalts m :=
  zipCycle_sound p1467 0 10 true (0) (by decide) cert1467 m hm
#print axioms never1467


/-- Third-level first-hole refinement 1468, 1RB---_1RC1RE_0RD---_1LD1RB_1RA0LB_------; entry 0, period 10. -/
def p1468 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1468 : zipCycle p1468 0 10 true (0) = true := by decide +kernel
theorem never1468 (m : Machine) (hm : compatible p1468 m) : NeverHalts m :=
  zipCycle_sound p1468 0 10 true (0) (by decide) cert1468 m hm
#print axioms never1468


/-- Third-level first-hole refinement 1469, 1RB---_1RC1RE_0RD---_1LD1RB_0LB0LB_------; entry 8, period 2. -/
def p1469 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1469 : zipCycle p1469 8 2 true (2) = true := by decide +kernel
theorem never1469 (m : Machine) (hm : compatible p1469 m) : NeverHalts m :=
  zipCycle_sound p1469 8 2 true (2) (by decide) cert1469 m hm
#print axioms never1469


/-- Third-level first-hole refinement 1470, 1RB---_1RC1RE_0RD---_1LD1RB_1LB0LB_------; entry 6, period 4. -/
def p1470 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1470 : zipCycle p1470 6 4 true (2) = true := by decide +kernel
theorem never1470 (m : Machine) (hm : compatible p1470 m) : NeverHalts m :=
  zipCycle_sound p1470 6 4 true (2) (by decide) cert1470 m hm
#print axioms never1470


/-- Third-level first-hole refinement 1471, 1RB---_1RC1RE_0RD---_1LD1RB_0RB0LB_------; entry 1, period 9. -/
def p1471 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1471 : zipCycle p1471 1 9 true (1) = true := by decide +kernel
theorem never1471 (m : Machine) (hm : compatible p1471 m) : NeverHalts m :=
  zipCycle_sound p1471 1 9 true (1) (by decide) cert1471 m hm
#print axioms never1471


/-- Third-level first-hole refinement 1472, 1RB---_1RC1RE_0RD---_1LD1RB_1RB0LB_------; entry 1, period 9. -/
def p1472 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1472 : zipCycle p1472 1 9 true (1) = true := by decide +kernel
theorem never1472 (m : Machine) (hm : compatible p1472 m) : NeverHalts m :=
  zipCycle_sound p1472 1 9 true (1) (by decide) cert1472 m hm
#print axioms never1472


/-- Third-level first-hole refinement 1473, 1RB---_1RC1RE_0RD---_1LD1RB_1RC0LB_------; entry 2, period 8. -/
def p1473 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1473 : zipCycle p1473 2 8 true (1) = true := by decide +kernel
theorem never1473 (m : Machine) (hm : compatible p1473 m) : NeverHalts m :=
  zipCycle_sound p1473 2 8 true (1) (by decide) cert1473 m hm
#print axioms never1473


/-- Third-level first-hole refinement 1474, 1RB---_1RC1RE_0RD---_1LD1RB_0LD0LB_------; entry 1, period 10. -/
def p1474 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1474 : zipCycle p1474 1 10 true (1) = true := by decide +kernel
theorem never1474 (m : Machine) (hm : compatible p1474 m) : NeverHalts m :=
  zipCycle_sound p1474 1 10 true (1) (by decide) cert1474 m hm
#print axioms never1474


/-- Third-level first-hole refinement 1475, 1RB---_1RC1RE_0RD---_1LD1RB_1LD0LB_------; entry 8, period 3. -/
def p1475 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1475 : zipCycle p1475 8 3 true (2) = true := by decide +kernel
theorem never1475 (m : Machine) (hm : compatible p1475 m) : NeverHalts m :=
  zipCycle_sound p1475 8 3 true (2) (by decide) cert1475 m hm
#print axioms never1475


/-- Third-level first-hole refinement 1476, 1RB---_1RC1RE_0RD---_1LD1RB_0RD0LB_------; entry 3, period 7. -/
def p1476 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1476 : zipCycle p1476 3 7 true (1) = true := by decide +kernel
theorem never1476 (m : Machine) (hm : compatible p1476 m) : NeverHalts m :=
  zipCycle_sound p1476 3 7 true (1) (by decide) cert1476 m hm
#print axioms never1476


/-- Third-level first-hole refinement 1477, 1RB---_1RC1RE_0RD---_1LD1RB_1RD0LB_------; entry 8, period 4. -/
def p1477 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1477 : zipCycle p1477 8 4 true (2) = true := by decide +kernel
theorem never1477 (m : Machine) (hm : compatible p1477 m) : NeverHalts m :=
  zipCycle_sound p1477 8 4 true (2) (by decide) cert1477 m hm
#print axioms never1477


/-- Third-level first-hole refinement 1478, 1RB---_1RC1RE_0RD---_1LD1RB_0LE0LB_------; entry 10, period 13. -/
def p1478 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1478 : zipCycle p1478 10 13 false (2) = true := by decide +kernel
theorem never1478 (m : Machine) (hm : compatible p1478 m) : NeverHalts m :=
  zipCycle_sound p1478 10 13 false (2) (by decide) cert1478 m hm
#print axioms never1478


/-- Third-level first-hole refinement 1479, 1RB---_1RC1RE_0RD---_1LD1RB_1LE0LB_------; entry 22, period 9. -/
def p1479 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1479 : zipCycle p1479 22 9 true (0) = true := by decide +kernel
theorem never1479 (m : Machine) (hm : compatible p1479 m) : NeverHalts m :=
  zipCycle_sound p1479 22 9 true (0) (by decide) cert1479 m hm
#print axioms never1479


/-- Third-level first-hole refinement 1480, 1RB---_1RC1RE_0RD---_1LD1RB_0RE0LB_------; entry 9, period 1. -/
def p1480 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1480 : zipCycle p1480 9 1 true (3) = true := by decide +kernel
theorem never1480 (m : Machine) (hm : compatible p1480 m) : NeverHalts m :=
  zipCycle_sound p1480 9 1 true (3) (by decide) cert1480 m hm
#print axioms never1480


/-- Third-level first-hole refinement 1481, 1RB---_1RC1RE_0RD---_1LD1RB_1RE0LB_------; entry 9, period 1. -/
def p1481 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert1481 : zipCycle p1481 9 1 true (3) = true := by decide +kernel
theorem never1481 (m : Machine) (hm : compatible p1481 m) : NeverHalts m :=
  zipCycle_sound p1481 9 1 true (3) (by decide) cert1481 m hm
#print axioms never1481


/-- Third-level first-hole refinement 1482, 1RB---_1RC1RE_0RD0RA_1LD1RB_---0LC_------; entry 0, period 9. -/
def p1482 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1482 : zipCycle p1482 0 9 true (0) = true := by decide +kernel
theorem never1482 (m : Machine) (hm : compatible p1482 m) : NeverHalts m :=
  zipCycle_sound p1482 0 9 true (0) (by decide) cert1482 m hm
#print axioms never1482


/-- Third-level first-hole refinement 1483, 1RB---_1RC1RE_0RD1RA_1LD1RB_---0LC_------; entry 0, period 9. -/
def p1483 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1483 : zipCycle p1483 0 9 true (0) = true := by decide +kernel
theorem never1483 (m : Machine) (hm : compatible p1483 m) : NeverHalts m :=
  zipCycle_sound p1483 0 9 true (0) (by decide) cert1483 m hm
#print axioms never1483


/-- Third-level first-hole refinement 1484, 1RB---_1RC1RE_0RD1LB_1LD1RB_---0LC_------; entry 11, period 5. -/
def p1484 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1484 : zipCycle p1484 11 5 false (1) = true := by decide +kernel
theorem never1484 (m : Machine) (hm : compatible p1484 m) : NeverHalts m :=
  zipCycle_sound p1484 11 5 false (1) (by decide) cert1484 m hm
#print axioms never1484


/-- Third-level first-hole refinement 1485, 1RB---_1RC1RE_0RD0RB_1LD1RB_---0LC_------; entry 1, period 8. -/
def p1485 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1485 : zipCycle p1485 1 8 true (1) = true := by decide +kernel
theorem never1485 (m : Machine) (hm : compatible p1485 m) : NeverHalts m :=
  zipCycle_sound p1485 1 8 true (1) (by decide) cert1485 m hm
#print axioms never1485


/-- Third-level first-hole refinement 1486, 1RB---_1RC1RE_0RD1RB_1LD1RB_---0LC_------; entry 1, period 8. -/
def p1486 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1486 : zipCycle p1486 1 8 true (1) = true := by decide +kernel
theorem never1486 (m : Machine) (hm : compatible p1486 m) : NeverHalts m :=
  zipCycle_sound p1486 1 8 true (1) (by decide) cert1486 m hm
#print axioms never1486


/-- Third-level first-hole refinement 1487, 1RB---_1RC1RE_0RD0LC_1LD1RB_---0LC_------; entry 12, period 1. -/
def p1487 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1487 : zipCycle p1487 12 1 false (0) = true := by decide +kernel
theorem never1487 (m : Machine) (hm : compatible p1487 m) : NeverHalts m :=
  zipCycle_sound p1487 12 1 false (0) (by decide) cert1487 m hm
#print axioms never1487


/-- Third-level first-hole refinement 1488, 1RB---_1RC1RE_0RD0RC_1LD1RB_---0LC_------; entry 1, period 18. -/
def p1488 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1488 : zipCycle p1488 1 18 true (1) = true := by decide +kernel
theorem never1488 (m : Machine) (hm : compatible p1488 m) : NeverHalts m :=
  zipCycle_sound p1488 1 18 true (1) (by decide) cert1488 m hm
#print axioms never1488


/-- Third-level first-hole refinement 1489, 1RB---_1RC1RE_0RD1RC_1LD1RB_---0LC_------; entry 2, period 7. -/
def p1489 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1489 : zipCycle p1489 2 7 true (1) = true := by decide +kernel
theorem never1489 (m : Machine) (hm : compatible p1489 m) : NeverHalts m :=
  zipCycle_sound p1489 2 7 true (1) (by decide) cert1489 m hm
#print axioms never1489


/-- Third-level first-hole refinement 1490, 1RB---_1RC1RE_0RD0LD_1LD1RB_---0LC_------; entry 1, period 9. -/
def p1490 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1490 : zipCycle p1490 1 9 true (1) = true := by decide +kernel
theorem never1490 (m : Machine) (hm : compatible p1490 m) : NeverHalts m :=
  zipCycle_sound p1490 1 9 true (1) (by decide) cert1490 m hm
#print axioms never1490


/-- Third-level first-hole refinement 1491, 1RB---_1RC1RE_0RD0RD_1LD1RB_---0LC_------; entry 3, period 6. -/
def p1491 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert1491 : zipCycle p1491 3 6 true (1) = true := by decide +kernel
theorem never1491 (m : Machine) (hm : compatible p1491 m) : NeverHalts m :=
  zipCycle_sound p1491 3 6 true (1) (by decide) cert1491 m hm
#print axioms never1491


/-- Third-level first-hole refinement 1492, 1RB---_1RC1RE_0RD1LB_1LD1RB_---1LC_------; entry 11, period 5. -/
def p1492 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1492 : zipCycle p1492 11 5 false (1) = true := by decide +kernel
theorem never1492 (m : Machine) (hm : compatible p1492 m) : NeverHalts m :=
  zipCycle_sound p1492 11 5 false (1) (by decide) cert1492 m hm
#print axioms never1492


/-- Third-level first-hole refinement 1493, 1RB---_1RC1RE_0RD0LC_1LD1RB_---1LC_------; entry 12, period 1. -/
def p1493 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1493 : zipCycle p1493 12 1 false (0) = true := by decide +kernel
theorem never1493 (m : Machine) (hm : compatible p1493 m) : NeverHalts m :=
  zipCycle_sound p1493 12 1 false (0) (by decide) cert1493 m hm
#print axioms never1493


/-- Third-level first-hole refinement 1494, 1RB---_1RC1RE_0RD1LC_1LD1RB_---1LC_------; entry 9, period 6. -/
def p1494 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1494 : zipCycle p1494 9 6 true (-1) = true := by decide +kernel
theorem never1494 (m : Machine) (hm : compatible p1494 m) : NeverHalts m :=
  zipCycle_sound p1494 9 6 true (-1) (by decide) cert1494 m hm
#print axioms never1494


/-- Third-level first-hole refinement 1495, 1RB---_1RC1RE_0RD1RC_1LD1RB_---1LC_------; entry 2, period 8. -/
def p1495 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1495 : zipCycle p1495 2 8 true (1) = true := by decide +kernel
theorem never1495 (m : Machine) (hm : compatible p1495 m) : NeverHalts m :=
  zipCycle_sound p1495 2 8 true (1) (by decide) cert1495 m hm
#print axioms never1495


/-- Third-level first-hole refinement 1496, 1RB---_1RC1RE_0RD0LD_1LD1RB_---1LC_------; entry 1, period 12. -/
def p1496 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1496 : zipCycle p1496 1 12 true (1) = true := by decide +kernel
theorem never1496 (m : Machine) (hm : compatible p1496 m) : NeverHalts m :=
  zipCycle_sound p1496 1 12 true (1) (by decide) cert1496 m hm
#print axioms never1496


/-- Third-level first-hole refinement 1497, 1RB---_1RC1RE_0RD1LD_1LD1RB_---1LC_------; entry 5, period 4. -/
def p1497 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1497 : zipCycle p1497 5 4 true (1) = true := by decide +kernel
theorem never1497 (m : Machine) (hm : compatible p1497 m) : NeverHalts m :=
  zipCycle_sound p1497 5 4 true (1) (by decide) cert1497 m hm
#print axioms never1497


/-- Third-level first-hole refinement 1498, 1RB---_1RC1RE_0RD0RD_1LD1RB_---1LC_------; entry 1, period 9. -/
def p1498 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1498 : zipCycle p1498 1 9 true (1) = true := by decide +kernel
theorem never1498 (m : Machine) (hm : compatible p1498 m) : NeverHalts m :=
  zipCycle_sound p1498 1 9 true (1) (by decide) cert1498 m hm
#print axioms never1498


/-- Third-level first-hole refinement 1499, 1RB---_1RC1RE_0RD1RD_1LD1RB_---1LC_------; entry 1, period 9. -/
def p1499 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert1499 : zipCycle p1499 1 9 true (1) = true := by decide +kernel
theorem never1499 (m : Machine) (hm : compatible p1499 m) : NeverHalts m :=
  zipCycle_sound p1499 1 9 true (1) (by decide) cert1499 m hm
#print axioms never1499

end BB6.Agent24Raw45D3_14
