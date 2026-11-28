import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_00
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 0, 1RB1LB_1RC0LA_0RD0LA_1LD1RB_------_------; entry 7, period 5. -/
def p0 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert0 : zipCycle p0 7 5 false (1) = true := by decide +kernel
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m :=
  zipCycle_sound p0 7 5 false (1) (by decide) cert0 m hm
#print axioms never0


/-- Third-level first-hole refinement 1, 1RB1LB_1RC0LA_0RD1LA_1LD1RB_------_------; entry 7, period 5. -/
def p1 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert1 : zipCycle p1 7 5 false (1) = true := by decide +kernel
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m :=
  zipCycle_sound p1 7 5 false (1) (by decide) cert1 m hm
#print axioms never1


/-- Third-level first-hole refinement 2, 1RB1LB_1RC0LA_0RD0RA_1LD1RB_------_------; entry 0, period 17. -/
def p2 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert2 : zipCycle p2 0 17 true (-1) = true := by decide +kernel
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m :=
  zipCycle_sound p2 0 17 true (-1) (by decide) cert2 m hm
#print axioms never2


/-- Third-level first-hole refinement 3, 1RB1LB_1RC0LA_0RD1RA_1LD1RB_------_------; entry 6, period 9. -/
def p3 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert3 : zipCycle p3 6 9 false (3) = true := by decide +kernel
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m :=
  zipCycle_sound p3 6 9 false (3) (by decide) cert3 m hm
#print axioms never3


/-- Third-level first-hole refinement 4, 1RB1LB_1RC0LA_0RD0LB_1LD1RB_------_------; entry 0, period 17. -/
def p4 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert4 : zipCycle p4 0 17 false (3) = true := by decide +kernel
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m :=
  zipCycle_sound p4 0 17 false (3) (by decide) cert4 m hm
#print axioms never4


/-- Third-level first-hole refinement 5, 1RB1LB_1RC0LA_0RD1LB_1LD1RB_------_------; entry 8, period 8. -/
def p5 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert5 : zipCycle p5 8 8 false (1) = true := by decide +kernel
theorem never5 (m : Machine) (hm : compatible p5 m) : NeverHalts m :=
  zipCycle_sound p5 8 8 false (1) (by decide) cert5 m hm
#print axioms never5


/-- Third-level first-hole refinement 6, 1RB1LB_1RC0LA_0RD0RB_1LD1RB_------_------; entry 10, period 11. -/
def p6 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert6 : zipCycle p6 10 11 true (0) = true := by decide +kernel
theorem never6 (m : Machine) (hm : compatible p6 m) : NeverHalts m :=
  zipCycle_sound p6 10 11 true (0) (by decide) cert6 m hm
#print axioms never6


/-- Third-level first-hole refinement 7, 1RB1LB_1RC0LA_0RD0LC_1LD1RB_------_------; entry 15, period 1. -/
def p7 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert7 : zipCycle p7 15 1 false (-1) = true := by decide +kernel
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m :=
  zipCycle_sound p7 15 1 false (-1) (by decide) cert7 m hm
#print axioms never7


/-- Third-level first-hole refinement 8, 1RB1LB_1RC0LA_0RD1LC_1LD1RB_------_------; entry 12, period 7. -/
def p8 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert8 : zipCycle p8 12 7 false (0) = true := by decide +kernel
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m :=
  zipCycle_sound p8 12 7 false (0) (by decide) cert8 m hm
#print axioms never8


/-- Third-level first-hole refinement 9, 1RB1LB_1RC0LA_0RD0RC_1LD1RB_------_------; entry 1, period 13. -/
def p9 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert9 : zipCycle p9 1 13 true (-1) = true := by decide +kernel
theorem never9 (m : Machine) (hm : compatible p9 m) : NeverHalts m :=
  zipCycle_sound p9 1 13 true (-1) (by decide) cert9 m hm
#print axioms never9


/-- Third-level first-hole refinement 10, 1RB1LB_1RC0LA_0RD1RC_1LD1RB_------_------; entry 1, period 13. -/
def p10 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert10 : zipCycle p10 1 13 true (-1) = true := by decide +kernel
theorem never10 (m : Machine) (hm : compatible p10 m) : NeverHalts m :=
  zipCycle_sound p10 1 13 true (-1) (by decide) cert10 m hm
#print axioms never10


/-- Third-level first-hole refinement 11, 1RB1LB_1RC0LA_0RD0LD_1LD1RB_------_------; entry 1, period 15. -/
def p11 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert11 : zipCycle p11 1 15 true (-1) = true := by decide +kernel
theorem never11 (m : Machine) (hm : compatible p11 m) : NeverHalts m :=
  zipCycle_sound p11 1 15 true (-1) (by decide) cert11 m hm
#print axioms never11


/-- Third-level first-hole refinement 12, 1RB1LB_1RC0LA_0RD1LD_1LD1RB_------_------; entry 5, period 7. -/
def p12 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert12 : zipCycle p12 5 7 false (2) = true := by decide +kernel
theorem never12 (m : Machine) (hm : compatible p12 m) : NeverHalts m :=
  zipCycle_sound p12 5 7 false (2) (by decide) cert12 m hm
#print axioms never12


/-- Third-level first-hole refinement 13, 1RB1LB_1RC0LA_0RD0RD_1LD1RB_------_------; entry 3, period 9. -/
def p13 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert13 : zipCycle p13 3 9 false (3) = true := by decide +kernel
theorem never13 (m : Machine) (hm : compatible p13 m) : NeverHalts m :=
  zipCycle_sound p13 3 9 false (3) (by decide) cert13 m hm
#print axioms never13


/-- Third-level first-hole refinement 14, 1RB1LB_1RC0LA_0RD1RD_1LD1RB_------_------; entry 4, period 16. -/
def p14 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert14 : zipCycle p14 4 16 false (2) = true := by decide +kernel
theorem never14 (m : Machine) (hm : compatible p14 m) : NeverHalts m :=
  zipCycle_sound p14 4 16 false (2) (by decide) cert14 m hm
#print axioms never14


/-- Third-level first-hole refinement 15, 1RB0RB_1RC0LA_0RD0LA_1LD1RB_------_------; entry 1, period 10. -/
def p15 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert15 : zipCycle p15 1 10 true (1) = true := by decide +kernel
theorem never15 (m : Machine) (hm : compatible p15 m) : NeverHalts m :=
  zipCycle_sound p15 1 10 true (1) (by decide) cert15 m hm
#print axioms never15


/-- Third-level first-hole refinement 16, 1RB0RB_1RC0LA_0RD1LA_1LD1RB_------_------; entry 0, period 12. -/
def p16 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert16 : zipCycle p16 0 12 true (0) = true := by decide +kernel
theorem never16 (m : Machine) (hm : compatible p16 m) : NeverHalts m :=
  zipCycle_sound p16 0 12 true (0) (by decide) cert16 m hm
#print axioms never16


/-- Third-level first-hole refinement 17, 1RB0RB_1RC0LA_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p17 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert17 : zipCycle p17 0 10 true (0) = true := by decide +kernel
theorem never17 (m : Machine) (hm : compatible p17 m) : NeverHalts m :=
  zipCycle_sound p17 0 10 true (0) (by decide) cert17 m hm
#print axioms never17


/-- Third-level first-hole refinement 18, 1RB0RB_1RC0LA_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p18 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert18 : zipCycle p18 0 10 true (0) = true := by decide +kernel
theorem never18 (m : Machine) (hm : compatible p18 m) : NeverHalts m :=
  zipCycle_sound p18 0 10 true (0) (by decide) cert18 m hm
#print axioms never18


/-- Third-level first-hole refinement 19, 1RB0RB_1RC0LA_0RD0LB_1LD1RB_------_------; entry 0, period 11. -/
def p19 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert19 : zipCycle p19 0 11 true (0) = true := by decide +kernel
theorem never19 (m : Machine) (hm : compatible p19 m) : NeverHalts m :=
  zipCycle_sound p19 0 11 true (0) (by decide) cert19 m hm
#print axioms never19


/-- Third-level first-hole refinement 20, 1RB0RB_1RC0LA_0RD1LB_1LD1RB_------_------; entry 6, period 8. -/
def p20 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert20 : zipCycle p20 6 8 true (1) = true := by decide +kernel
theorem never20 (m : Machine) (hm : compatible p20 m) : NeverHalts m :=
  zipCycle_sound p20 6 8 true (1) (by decide) cert20 m hm
#print axioms never20


/-- Third-level first-hole refinement 21, 1RB0RB_1RC0LA_0RD0RB_1LD1RB_------_------; entry 1, period 9. -/
def p21 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert21 : zipCycle p21 1 9 true (1) = true := by decide +kernel
theorem never21 (m : Machine) (hm : compatible p21 m) : NeverHalts m :=
  zipCycle_sound p21 1 9 true (1) (by decide) cert21 m hm
#print axioms never21


/-- Third-level first-hole refinement 22, 1RB0RB_1RC0LA_0RD1RB_1LD1RB_------_------; entry 1, period 9. -/
def p22 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert22 : zipCycle p22 1 9 true (1) = true := by decide +kernel
theorem never22 (m : Machine) (hm : compatible p22 m) : NeverHalts m :=
  zipCycle_sound p22 1 9 true (1) (by decide) cert22 m hm
#print axioms never22


/-- Third-level first-hole refinement 23, 1RB0RB_1RC0LA_0RD0LC_1LD1RB_------_------; entry 21, period 1. -/
def p23 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert23 : zipCycle p23 21 1 false (1) = true := by decide +kernel
theorem never23 (m : Machine) (hm : compatible p23 m) : NeverHalts m :=
  zipCycle_sound p23 21 1 false (1) (by decide) cert23 m hm
#print axioms never23


/-- Third-level first-hole refinement 24, 1RB0RB_1RC0LA_0RD1LC_1LD1RB_------_------; entry 1, period 14. -/
def p24 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert24 : zipCycle p24 1 14 true (1) = true := by decide +kernel
theorem never24 (m : Machine) (hm : compatible p24 m) : NeverHalts m :=
  zipCycle_sound p24 1 14 true (1) (by decide) cert24 m hm
#print axioms never24


/-- Third-level first-hole refinement 25, 1RB0RB_1RC0LA_0RD1RC_1LD1RB_------_------; entry 2, period 8. -/
def p25 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert25 : zipCycle p25 2 8 true (1) = true := by decide +kernel
theorem never25 (m : Machine) (hm : compatible p25 m) : NeverHalts m :=
  zipCycle_sound p25 2 8 true (1) (by decide) cert25 m hm
#print axioms never25


/-- Third-level first-hole refinement 26, 1RB0RB_1RC0LA_0RD0LD_1LD1RB_------_------; entry 1, period 10. -/
def p26 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert26 : zipCycle p26 1 10 true (1) = true := by decide +kernel
theorem never26 (m : Machine) (hm : compatible p26 m) : NeverHalts m :=
  zipCycle_sound p26 1 10 true (1) (by decide) cert26 m hm
#print axioms never26


/-- Third-level first-hole refinement 27, 1RB0RB_1RC0LA_0RD1LD_1LD1RB_------_------; entry 1, period 12. -/
def p27 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert27 : zipCycle p27 1 12 true (1) = true := by decide +kernel
theorem never27 (m : Machine) (hm : compatible p27 m) : NeverHalts m :=
  zipCycle_sound p27 1 12 true (1) (by decide) cert27 m hm
#print axioms never27


/-- Third-level first-hole refinement 28, 1RB0RB_1RC0LA_0RD0RD_1LD1RB_------_------; entry 3, period 7. -/
def p28 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert28 : zipCycle p28 3 7 true (1) = true := by decide +kernel
theorem never28 (m : Machine) (hm : compatible p28 m) : NeverHalts m :=
  zipCycle_sound p28 3 7 true (1) (by decide) cert28 m hm
#print axioms never28


/-- Third-level first-hole refinement 29, 1RB0RB_1RC0LA_0RD1RD_1LD1RB_------_------; entry 1, period 13. -/
def p29 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert29 : zipCycle p29 1 13 true (1) = true := by decide +kernel
theorem never29 (m : Machine) (hm : compatible p29 m) : NeverHalts m :=
  zipCycle_sound p29 1 13 true (1) (by decide) cert29 m hm
#print axioms never29


/-- Third-level first-hole refinement 30, 1RB1RB_1RC0LA_0RD0LA_1LD1RB_------_------; entry 1, period 10. -/
def p30 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert30 : zipCycle p30 1 10 true (1) = true := by decide +kernel
theorem never30 (m : Machine) (hm : compatible p30 m) : NeverHalts m :=
  zipCycle_sound p30 1 10 true (1) (by decide) cert30 m hm
#print axioms never30


/-- Third-level first-hole refinement 31, 1RB1RB_1RC0LA_0RD1LA_1LD1RB_------_------; entry 1, period 12. -/
def p31 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert31 : zipCycle p31 1 12 true (1) = true := by decide +kernel
theorem never31 (m : Machine) (hm : compatible p31 m) : NeverHalts m :=
  zipCycle_sound p31 1 12 true (1) (by decide) cert31 m hm
#print axioms never31


/-- Third-level first-hole refinement 32, 1RB1RB_1RC0LA_0RD0RA_1LD1RB_------_------; entry 0, period 10. -/
def p32 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert32 : zipCycle p32 0 10 true (0) = true := by decide +kernel
theorem never32 (m : Machine) (hm : compatible p32 m) : NeverHalts m :=
  zipCycle_sound p32 0 10 true (0) (by decide) cert32 m hm
#print axioms never32


/-- Third-level first-hole refinement 33, 1RB1RB_1RC0LA_0RD1RA_1LD1RB_------_------; entry 0, period 10. -/
def p33 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert33 : zipCycle p33 0 10 true (0) = true := by decide +kernel
theorem never33 (m : Machine) (hm : compatible p33 m) : NeverHalts m :=
  zipCycle_sound p33 0 10 true (0) (by decide) cert33 m hm
#print axioms never33


/-- Third-level first-hole refinement 34, 1RB1RB_1RC0LA_0RD0LB_1LD1RB_------_------; entry 1, period 11. -/
def p34 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert34 : zipCycle p34 1 11 true (1) = true := by decide +kernel
theorem never34 (m : Machine) (hm : compatible p34 m) : NeverHalts m :=
  zipCycle_sound p34 1 11 true (1) (by decide) cert34 m hm
#print axioms never34


/-- Third-level first-hole refinement 35, 1RB1RB_1RC0LA_0RD1LB_1LD1RB_------_------; entry 6, period 4. -/
def p35 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert35 : zipCycle p35 6 4 true (1) = true := by decide +kernel
theorem never35 (m : Machine) (hm : compatible p35 m) : NeverHalts m :=
  zipCycle_sound p35 6 4 true (1) (by decide) cert35 m hm
#print axioms never35


/-- Third-level first-hole refinement 36, 1RB1RB_1RC0LA_0RD0RB_1LD1RB_------_------; entry 1, period 9. -/
def p36 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert36 : zipCycle p36 1 9 true (1) = true := by decide +kernel
theorem never36 (m : Machine) (hm : compatible p36 m) : NeverHalts m :=
  zipCycle_sound p36 1 9 true (1) (by decide) cert36 m hm
#print axioms never36


/-- Third-level first-hole refinement 37, 1RB1RB_1RC0LA_0RD1RB_1LD1RB_------_------; entry 1, period 9. -/
def p37 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert37 : zipCycle p37 1 9 true (1) = true := by decide +kernel
theorem never37 (m : Machine) (hm : compatible p37 m) : NeverHalts m :=
  zipCycle_sound p37 1 9 true (1) (by decide) cert37 m hm
#print axioms never37


/-- Third-level first-hole refinement 38, 1RB1RB_1RC0LA_0RD0LC_1LD1RB_------_------; entry 14, period 1. -/
def p38 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert38 : zipCycle p38 14 1 false (0) = true := by decide +kernel
theorem never38 (m : Machine) (hm : compatible p38 m) : NeverHalts m :=
  zipCycle_sound p38 14 1 false (0) (by decide) cert38 m hm
#print axioms never38


/-- Third-level first-hole refinement 39, 1RB1RB_1RC0LA_0RD1LC_1LD1RB_------_------; entry 10, period 8. -/
def p39 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert39 : zipCycle p39 10 8 true (-1) = true := by decide +kernel
theorem never39 (m : Machine) (hm : compatible p39 m) : NeverHalts m :=
  zipCycle_sound p39 10 8 true (-1) (by decide) cert39 m hm
#print axioms never39


/-- Third-level first-hole refinement 40, 1RB1RB_1RC0LA_0RD1RC_1LD1RB_------_------; entry 2, period 8. -/
def p40 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert40 : zipCycle p40 2 8 true (1) = true := by decide +kernel
theorem never40 (m : Machine) (hm : compatible p40 m) : NeverHalts m :=
  zipCycle_sound p40 2 8 true (1) (by decide) cert40 m hm
#print axioms never40


/-- Third-level first-hole refinement 41, 1RB1RB_1RC0LA_0RD0LD_1LD1RB_------_------; entry 1, period 10. -/
def p41 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert41 : zipCycle p41 1 10 true (1) = true := by decide +kernel
theorem never41 (m : Machine) (hm : compatible p41 m) : NeverHalts m :=
  zipCycle_sound p41 1 10 true (1) (by decide) cert41 m hm
#print axioms never41


/-- Third-level first-hole refinement 42, 1RB1RB_1RC0LA_0RD1LD_1LD1RB_------_------; entry 1, period 12. -/
def p42 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert42 : zipCycle p42 1 12 true (1) = true := by decide +kernel
theorem never42 (m : Machine) (hm : compatible p42 m) : NeverHalts m :=
  zipCycle_sound p42 1 12 true (1) (by decide) cert42 m hm
#print axioms never42


/-- Third-level first-hole refinement 43, 1RB1RB_1RC0LA_0RD0RD_1LD1RB_------_------; entry 3, period 7. -/
def p43 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert43 : zipCycle p43 3 7 true (1) = true := by decide +kernel
theorem never43 (m : Machine) (hm : compatible p43 m) : NeverHalts m :=
  zipCycle_sound p43 3 7 true (1) (by decide) cert43 m hm
#print axioms never43


/-- Third-level first-hole refinement 44, 1RB1RB_1RC0LA_0RD1RD_1LD1RB_------_------; entry 1, period 13. -/
def p44 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert44 : zipCycle p44 1 13 true (1) = true := by decide +kernel
theorem never44 (m : Machine) (hm : compatible p44 m) : NeverHalts m :=
  zipCycle_sound p44 1 13 true (1) (by decide) cert44 m hm
#print axioms never44


/-- Third-level first-hole refinement 45, 1RB0LC_1RC0LA_0RD0LA_1LD1RB_------_------; entry 0, period 9. -/
def p45 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert45 : zipCycle p45 0 9 false (3) = true := by decide +kernel
theorem never45 (m : Machine) (hm : compatible p45 m) : NeverHalts m :=
  zipCycle_sound p45 0 9 false (3) (by decide) cert45 m hm
#print axioms never45


/-- Third-level first-hole refinement 46, 1RB0LC_1RC0LA_0RD1LA_1LD1RB_------_------; entry 13, period 1. -/
def p46 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert46 : zipCycle p46 13 1 false (-1) = true := by decide +kernel
theorem never46 (m : Machine) (hm : compatible p46 m) : NeverHalts m :=
  zipCycle_sound p46 13 1 false (-1) (by decide) cert46 m hm
#print axioms never46


/-- Third-level first-hole refinement 47, 1RB0LC_1RC0LA_0RD0RA_1LD1RB_------_------; entry 0, period 12. -/
def p47 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert47 : zipCycle p47 0 12 true (0) = true := by decide +kernel
theorem never47 (m : Machine) (hm : compatible p47 m) : NeverHalts m :=
  zipCycle_sound p47 0 12 true (0) (by decide) cert47 m hm
#print axioms never47


/-- Third-level first-hole refinement 48, 1RB0LC_1RC0LA_0RD1RA_1LD1RB_------_------; entry 0, period 12. -/
def p48 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert48 : zipCycle p48 0 12 true (0) = true := by decide +kernel
theorem never48 (m : Machine) (hm : compatible p48 m) : NeverHalts m :=
  zipCycle_sound p48 0 12 true (0) (by decide) cert48 m hm
#print axioms never48


/-- Third-level first-hole refinement 49, 1RB0LC_1RC0LA_0RD0LB_1LD1RB_------_------; entry 17, period 1. -/
def p49 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert49 : zipCycle p49 17 1 false (-1) = true := by decide +kernel
theorem never49 (m : Machine) (hm : compatible p49 m) : NeverHalts m :=
  zipCycle_sound p49 17 1 false (-1) (by decide) cert49 m hm
#print axioms never49


/-- Third-level first-hole refinement 50, 1RB0LC_1RC0LA_0RD1LB_1LD1RB_------_------; entry 18, period 1. -/
def p50 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert50 : zipCycle p50 18 1 false (-2) = true := by decide +kernel
theorem never50 (m : Machine) (hm : compatible p50 m) : NeverHalts m :=
  zipCycle_sound p50 18 1 false (-2) (by decide) cert50 m hm
#print axioms never50


/-- Third-level first-hole refinement 51, 1RB0LC_1RC0LA_0RD0RB_1LD1RB_------_------; entry 1, period 11. -/
def p51 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert51 : zipCycle p51 1 11 true (0) = true := by decide +kernel
theorem never51 (m : Machine) (hm : compatible p51 m) : NeverHalts m :=
  zipCycle_sound p51 1 11 true (0) (by decide) cert51 m hm
#print axioms never51


/-- Third-level first-hole refinement 52, 1RB0LC_1RC0LA_0RD1RB_1LD1RB_------_------; entry 1, period 11. -/
def p52 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert52 : zipCycle p52 1 11 true (0) = true := by decide +kernel
theorem never52 (m : Machine) (hm : compatible p52 m) : NeverHalts m :=
  zipCycle_sound p52 1 11 true (0) (by decide) cert52 m hm
#print axioms never52


/-- Third-level first-hole refinement 53, 1RB0LC_1RC0LA_0RD0LC_1LD1RB_------_------; entry 10, period 1. -/
def p53 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert53 : zipCycle p53 10 1 false (0) = true := by decide +kernel
theorem never53 (m : Machine) (hm : compatible p53 m) : NeverHalts m :=
  zipCycle_sound p53 10 1 false (0) (by decide) cert53 m hm
#print axioms never53


/-- Third-level first-hole refinement 54, 1RB0LC_1RC0LA_0RD1LC_1LD1RB_------_------; entry 1, period 13. -/
def p54 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert54 : zipCycle p54 1 13 true (-1) = true := by decide +kernel
theorem never54 (m : Machine) (hm : compatible p54 m) : NeverHalts m :=
  zipCycle_sound p54 1 13 true (-1) (by decide) cert54 m hm
#print axioms never54


/-- Third-level first-hole refinement 55, 1RB0LC_1RC0LA_0RD0RC_1LD1RB_------_------; entry 10, period 1. -/
def p55 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert55 : zipCycle p55 10 1 false (2) = true := by decide +kernel
theorem never55 (m : Machine) (hm : compatible p55 m) : NeverHalts m :=
  zipCycle_sound p55 10 1 false (2) (by decide) cert55 m hm
#print axioms never55


/-- Third-level first-hole refinement 56, 1RB0LC_1RC0LA_0RD1RC_1LD1RB_------_------; entry 16, period 1. -/
def p56 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert56 : zipCycle p56 16 1 false (0) = true := by decide +kernel
theorem never56 (m : Machine) (hm : compatible p56 m) : NeverHalts m :=
  zipCycle_sound p56 16 1 false (0) (by decide) cert56 m hm
#print axioms never56


/-- Third-level first-hole refinement 57, 1RB0LC_1RC0LA_0RD0LD_1LD1RB_------_------; entry 9, period 1. -/
def p57 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert57 : zipCycle p57 9 1 false (-1) = true := by decide +kernel
theorem never57 (m : Machine) (hm : compatible p57 m) : NeverHalts m :=
  zipCycle_sound p57 9 1 false (-1) (by decide) cert57 m hm
#print axioms never57


/-- Third-level first-hole refinement 58, 1RB0LC_1RC0LA_0RD1LD_1LD1RB_------_------; entry 9, period 1. -/
def p58 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert58 : zipCycle p58 9 1 false (-1) = true := by decide +kernel
theorem never58 (m : Machine) (hm : compatible p58 m) : NeverHalts m :=
  zipCycle_sound p58 9 1 false (-1) (by decide) cert58 m hm
#print axioms never58


/-- Third-level first-hole refinement 59, 1RB0LC_1RC0LA_0RD0RD_1LD1RB_------_------; entry 9, period 1. -/
def p59 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert59 : zipCycle p59 9 1 false (1) = true := by decide +kernel
theorem never59 (m : Machine) (hm : compatible p59 m) : NeverHalts m :=
  zipCycle_sound p59 9 1 false (1) (by decide) cert59 m hm
#print axioms never59


/-- Third-level first-hole refinement 60, 1RB0LC_1RC0LA_0RD1RD_1LD1RB_------_------; entry 14, period 1. -/
def p60 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert60 : zipCycle p60 14 1 false (0) = true := by decide +kernel
theorem never60 (m : Machine) (hm : compatible p60 m) : NeverHalts m :=
  zipCycle_sound p60 14 1 false (0) (by decide) cert60 m hm
#print axioms never60


/-- Third-level first-hole refinement 61, 1RB1LC_1RC0LA_0RD0LA_1LD1RB_------_------; entry 7, period 5. -/
def p61 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert61 : zipCycle p61 7 5 false (1) = true := by decide +kernel
theorem never61 (m : Machine) (hm : compatible p61 m) : NeverHalts m :=
  zipCycle_sound p61 7 5 false (1) (by decide) cert61 m hm
#print axioms never61


/-- Third-level first-hole refinement 62, 1RB1LC_1RC0LA_0RD1LA_1LD1RB_------_------; entry 7, period 9. -/
def p62 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert62 : zipCycle p62 7 9 false (1) = true := by decide +kernel
theorem never62 (m : Machine) (hm : compatible p62 m) : NeverHalts m :=
  zipCycle_sound p62 7 9 false (1) (by decide) cert62 m hm
#print axioms never62


/-- Third-level first-hole refinement 63, 1RB1LC_1RC0LA_0RD0RA_1LD1RB_------_------; entry 0, period 14. -/
def p63 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert63 : zipCycle p63 0 14 true (0) = true := by decide +kernel
theorem never63 (m : Machine) (hm : compatible p63 m) : NeverHalts m :=
  zipCycle_sound p63 0 14 true (0) (by decide) cert63 m hm
#print axioms never63


/-- Third-level first-hole refinement 64, 1RB1LC_1RC0LA_0RD1RA_1LD1RB_------_------; entry 7, period 2. -/
def p64 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert64 : zipCycle p64 7 2 true (0) = true := by decide +kernel
theorem never64 (m : Machine) (hm : compatible p64 m) : NeverHalts m :=
  zipCycle_sound p64 7 2 true (0) (by decide) cert64 m hm
#print axioms never64


/-- Third-level first-hole refinement 65, 1RB1LC_1RC0LA_0RD0LB_1LD1RB_------_------; entry 1, period 17. -/
def p65 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert65 : zipCycle p65 1 17 true (-1) = true := by decide +kernel
theorem never65 (m : Machine) (hm : compatible p65 m) : NeverHalts m :=
  zipCycle_sound p65 1 17 true (-1) (by decide) cert65 m hm
#print axioms never65


/-- Third-level first-hole refinement 66, 1RB1LC_1RC0LA_0RD1LB_1LD1RB_------_------; entry 13, period 6. -/
def p66 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert66 : zipCycle p66 13 6 true (-3) = true := by decide +kernel
theorem never66 (m : Machine) (hm : compatible p66 m) : NeverHalts m :=
  zipCycle_sound p66 13 6 true (-3) (by decide) cert66 m hm
#print axioms never66


/-- Third-level first-hole refinement 67, 1RB1LC_1RC0LA_0RD0RB_1LD1RB_------_------; entry 1, period 13. -/
def p67 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert67 : zipCycle p67 1 13 true (0) = true := by decide +kernel
theorem never67 (m : Machine) (hm : compatible p67 m) : NeverHalts m :=
  zipCycle_sound p67 1 13 true (0) (by decide) cert67 m hm
#print axioms never67


/-- Third-level first-hole refinement 68, 1RB1LC_1RC0LA_0RD1RB_1LD1RB_------_------; entry 1, period 15. -/
def p68 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert68 : zipCycle p68 1 15 true (-1) = true := by decide +kernel
theorem never68 (m : Machine) (hm : compatible p68 m) : NeverHalts m :=
  zipCycle_sound p68 1 15 true (-1) (by decide) cert68 m hm
#print axioms never68


/-- Third-level first-hole refinement 69, 1RB1LC_1RC0LA_0RD0LC_1LD1RB_------_------; entry 10, period 1. -/
def p69 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert69 : zipCycle p69 10 1 false (0) = true := by decide +kernel
theorem never69 (m : Machine) (hm : compatible p69 m) : NeverHalts m :=
  zipCycle_sound p69 10 1 false (0) (by decide) cert69 m hm
#print axioms never69


/-- Third-level first-hole refinement 70, 1RB1LC_1RC0LA_0RD1LC_1LD1RB_------_------; entry 1, period 17. -/
def p70 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert70 : zipCycle p70 1 17 true (-1) = true := by decide +kernel
theorem never70 (m : Machine) (hm : compatible p70 m) : NeverHalts m :=
  zipCycle_sound p70 1 17 true (-1) (by decide) cert70 m hm
#print axioms never70


/-- Third-level first-hole refinement 71, 1RB1LC_1RC0LA_0RD0RC_1LD1RB_------_------; entry 1, period 11. -/
def p71 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert71 : zipCycle p71 1 11 true (0) = true := by decide +kernel
theorem never71 (m : Machine) (hm : compatible p71 m) : NeverHalts m :=
  zipCycle_sound p71 1 11 true (0) (by decide) cert71 m hm
#print axioms never71


/-- Third-level first-hole refinement 72, 1RB1LC_1RC0LA_0RD1RC_1LD1RB_------_------; entry 1, period 11. -/
def p72 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert72 : zipCycle p72 1 11 true (0) = true := by decide +kernel
theorem never72 (m : Machine) (hm : compatible p72 m) : NeverHalts m :=
  zipCycle_sound p72 1 11 true (0) (by decide) cert72 m hm
#print axioms never72


/-- Third-level first-hole refinement 73, 1RB1LC_1RC0LA_0RD0LD_1LD1RB_------_------; entry 9, period 1. -/
def p73 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert73 : zipCycle p73 9 1 false (-1) = true := by decide +kernel
theorem never73 (m : Machine) (hm : compatible p73 m) : NeverHalts m :=
  zipCycle_sound p73 9 1 false (-1) (by decide) cert73 m hm
#print axioms never73


/-- Third-level first-hole refinement 74, 1RB1LC_1RC0LA_0RD1LD_1LD1RB_------_------; entry 9, period 1. -/
def p74 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert74 : zipCycle p74 9 1 false (-1) = true := by decide +kernel
theorem never74 (m : Machine) (hm : compatible p74 m) : NeverHalts m :=
  zipCycle_sound p74 9 1 false (-1) (by decide) cert74 m hm
#print axioms never74


/-- Third-level first-hole refinement 75, 1RB1LC_1RC0LA_0RD0RD_1LD1RB_------_------; entry 3, period 9. -/
def p75 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert75 : zipCycle p75 3 9 true (0) = true := by decide +kernel
theorem never75 (m : Machine) (hm : compatible p75 m) : NeverHalts m :=
  zipCycle_sound p75 3 9 true (0) (by decide) cert75 m hm
#print axioms never75


/-- Third-level first-hole refinement 76, 1RB1LC_1RC0LA_0RD1RD_1LD1RB_------_------; entry 1, period 17. -/
def p76 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert76 : zipCycle p76 1 17 true (0) = true := by decide +kernel
theorem never76 (m : Machine) (hm : compatible p76 m) : NeverHalts m :=
  zipCycle_sound p76 1 17 true (0) (by decide) cert76 m hm
#print axioms never76


/-- Third-level first-hole refinement 77, 1RB0LE_1RC0LA_0RD---_1LD1RB_---0LA_------; entry 0, period 9. -/
def p77 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert77 : zipCycle p77 0 9 false (3) = true := by decide +kernel
theorem never77 (m : Machine) (hm : compatible p77 m) : NeverHalts m :=
  zipCycle_sound p77 0 9 false (3) (by decide) cert77 m hm
#print axioms never77


/-- Third-level first-hole refinement 78, 1RB0LE_1RC0LA_0RD---_1LD1RB_---0RB_------; entry 1, period 11. -/
def p78 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert78 : zipCycle p78 1 11 true (0) = true := by decide +kernel
theorem never78 (m : Machine) (hm : compatible p78 m) : NeverHalts m :=
  zipCycle_sound p78 1 11 true (0) (by decide) cert78 m hm
#print axioms never78


/-- Third-level first-hole refinement 79, 1RB0LE_1RC0LA_0RD---_1LD1RB_---1RB_------; entry 1, period 11. -/
def p79 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert79 : zipCycle p79 1 11 true (0) = true := by decide +kernel
theorem never79 (m : Machine) (hm : compatible p79 m) : NeverHalts m :=
  zipCycle_sound p79 1 11 true (0) (by decide) cert79 m hm
#print axioms never79


/-- Third-level first-hole refinement 80, 1RB0LE_1RC0LA_0RD---_1LD1RB_---0LC_------; entry 10, period 1. -/
def p80 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert80 : zipCycle p80 10 1 false (0) = true := by decide +kernel
theorem never80 (m : Machine) (hm : compatible p80 m) : NeverHalts m :=
  zipCycle_sound p80 10 1 false (0) (by decide) cert80 m hm
#print axioms never80


/-- Third-level first-hole refinement 81, 1RB0LE_1RC0LA_0RD---_1LD1RB_---1LC_------; entry 1, period 13. -/
def p81 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert81 : zipCycle p81 1 13 true (-1) = true := by decide +kernel
theorem never81 (m : Machine) (hm : compatible p81 m) : NeverHalts m :=
  zipCycle_sound p81 1 13 true (-1) (by decide) cert81 m hm
#print axioms never81


/-- Third-level first-hole refinement 82, 1RB0LE_1RC0LA_0RD---_1LD1RB_---0RC_------; entry 10, period 1. -/
def p82 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert82 : zipCycle p82 10 1 false (2) = true := by decide +kernel
theorem never82 (m : Machine) (hm : compatible p82 m) : NeverHalts m :=
  zipCycle_sound p82 10 1 false (2) (by decide) cert82 m hm
#print axioms never82


/-- Third-level first-hole refinement 83, 1RB0LE_1RC0LA_0RD---_1LD1RB_---0LD_------; entry 9, period 1. -/
def p83 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert83 : zipCycle p83 9 1 false (-1) = true := by decide +kernel
theorem never83 (m : Machine) (hm : compatible p83 m) : NeverHalts m :=
  zipCycle_sound p83 9 1 false (-1) (by decide) cert83 m hm
#print axioms never83


/-- Third-level first-hole refinement 84, 1RB0LE_1RC0LA_0RD---_1LD1RB_---1LD_------; entry 9, period 1. -/
def p84 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert84 : zipCycle p84 9 1 false (-1) = true := by decide +kernel
theorem never84 (m : Machine) (hm : compatible p84 m) : NeverHalts m :=
  zipCycle_sound p84 9 1 false (-1) (by decide) cert84 m hm
#print axioms never84


/-- Third-level first-hole refinement 85, 1RB0LE_1RC0LA_0RD---_1LD1RB_---0RD_------; entry 9, period 1. -/
def p85 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert85 : zipCycle p85 9 1 false (1) = true := by decide +kernel
theorem never85 (m : Machine) (hm : compatible p85 m) : NeverHalts m :=
  zipCycle_sound p85 9 1 false (1) (by decide) cert85 m hm
#print axioms never85


/-- Third-level first-hole refinement 86, 1RB1LE_1RC0LA_0RD---_1LD1RB_---1RA_------; entry 7, period 2. -/
def p86 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert86 : zipCycle p86 7 2 true (0) = true := by decide +kernel
theorem never86 (m : Machine) (hm : compatible p86 m) : NeverHalts m :=
  zipCycle_sound p86 7 2 true (0) (by decide) cert86 m hm
#print axioms never86


/-- Third-level first-hole refinement 87, 1RB1LE_1RC0LA_0RD---_1LD1RB_---0RB_------; entry 1, period 13. -/
def p87 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert87 : zipCycle p87 1 13 true (0) = true := by decide +kernel
theorem never87 (m : Machine) (hm : compatible p87 m) : NeverHalts m :=
  zipCycle_sound p87 1 13 true (0) (by decide) cert87 m hm
#print axioms never87


/-- Third-level first-hole refinement 88, 1RB1LE_1RC0LA_0RD---_1LD1RB_---0LC_------; entry 10, period 1. -/
def p88 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert88 : zipCycle p88 10 1 false (0) = true := by decide +kernel
theorem never88 (m : Machine) (hm : compatible p88 m) : NeverHalts m :=
  zipCycle_sound p88 10 1 false (0) (by decide) cert88 m hm
#print axioms never88


/-- Third-level first-hole refinement 89, 1RB1LE_1RC0LA_0RD---_1LD1RB_---0LD_------; entry 9, period 1. -/
def p89 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert89 : zipCycle p89 9 1 false (-1) = true := by decide +kernel
theorem never89 (m : Machine) (hm : compatible p89 m) : NeverHalts m :=
  zipCycle_sound p89 9 1 false (-1) (by decide) cert89 m hm
#print axioms never89


/-- Third-level first-hole refinement 90, 1RB1LE_1RC0LA_0RD---_1LD1RB_---1LD_------; entry 9, period 1. -/
def p90 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert90 : zipCycle p90 9 1 false (-1) = true := by decide +kernel
theorem never90 (m : Machine) (hm : compatible p90 m) : NeverHalts m :=
  zipCycle_sound p90 9 1 false (-1) (by decide) cert90 m hm
#print axioms never90


/-- Third-level first-hole refinement 91, 1RB0RE_1RC0LA_0RD---_1LD1RB_1LA---_------; entry 6, period 4. -/
def p91 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert91 : zipCycle p91 6 4 true (1) = true := by decide +kernel
theorem never91 (m : Machine) (hm : compatible p91 m) : NeverHalts m :=
  zipCycle_sound p91 6 4 true (1) (by decide) cert91 m hm
#print axioms never91


/-- Third-level first-hole refinement 92, 1RB0RE_1RC0LA_0RD---_1LD1RB_0RA---_------; entry 0, period 11. -/
def p92 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert92 : zipCycle p92 0 11 true (0) = true := by decide +kernel
theorem never92 (m : Machine) (hm : compatible p92 m) : NeverHalts m :=
  zipCycle_sound p92 0 11 true (0) (by decide) cert92 m hm
#print axioms never92


/-- Third-level first-hole refinement 93, 1RB0RE_1RC0LA_0RD---_1LD1RB_1RA---_------; entry 0, period 11. -/
def p93 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert93 : zipCycle p93 0 11 true (0) = true := by decide +kernel
theorem never93 (m : Machine) (hm : compatible p93 m) : NeverHalts m :=
  zipCycle_sound p93 0 11 true (0) (by decide) cert93 m hm
#print axioms never93


/-- Third-level first-hole refinement 94, 1RB0RE_1RC0LA_0RD---_1LD1RB_0LB---_------; entry 1, period 11. -/
def p94 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert94 : zipCycle p94 1 11 true (1) = true := by decide +kernel
theorem never94 (m : Machine) (hm : compatible p94 m) : NeverHalts m :=
  zipCycle_sound p94 1 11 true (1) (by decide) cert94 m hm
#print axioms never94


/-- Third-level first-hole refinement 95, 1RB0RE_1RC0LA_0RD---_1LD1RB_0RB---_------; entry 0, period 10. -/
def p95 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert95 : zipCycle p95 0 10 true (0) = true := by decide +kernel
theorem never95 (m : Machine) (hm : compatible p95 m) : NeverHalts m :=
  zipCycle_sound p95 0 10 true (0) (by decide) cert95 m hm
#print axioms never95


/-- Third-level first-hole refinement 96, 1RB0RE_1RC0LA_0RD---_1LD1RB_1RB---_------; entry 1, period 11. -/
def p96 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert96 : zipCycle p96 1 11 true (1) = true := by decide +kernel
theorem never96 (m : Machine) (hm : compatible p96 m) : NeverHalts m :=
  zipCycle_sound p96 1 11 true (1) (by decide) cert96 m hm
#print axioms never96


/-- Third-level first-hole refinement 97, 1RB0RE_1RC0LA_0RD---_1LD1RB_0LC---_------; entry 17, period 1. -/
def p97 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert97 : zipCycle p97 17 1 false (1) = true := by decide +kernel
theorem never97 (m : Machine) (hm : compatible p97 m) : NeverHalts m :=
  zipCycle_sound p97 17 1 false (1) (by decide) cert97 m hm
#print axioms never97


/-- Third-level first-hole refinement 98, 1RB0RE_1RC0LA_0RD---_1LD1RB_1LC---_------; entry 1, period 15. -/
def p98 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert98 : zipCycle p98 1 15 true (1) = true := by decide +kernel
theorem never98 (m : Machine) (hm : compatible p98 m) : NeverHalts m :=
  zipCycle_sound p98 1 15 true (1) (by decide) cert98 m hm
#print axioms never98


/-- Third-level first-hole refinement 99, 1RB0RE_1RC0LA_0RD---_1LD1RB_0LD---_------; entry 14, period 1. -/
def p99 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert99 : zipCycle p99 14 1 false (0) = true := by decide +kernel
theorem never99 (m : Machine) (hm : compatible p99 m) : NeverHalts m :=
  zipCycle_sound p99 14 1 false (0) (by decide) cert99 m hm
#print axioms never99

end BB6.Agent24Raw45D3_00
