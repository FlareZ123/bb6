import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D2A
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Raw45 first-hole depth 2, 1RB0LA_1RC0LA_0RD---_1LD1RB_------_------. -/
def p0 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert0 : zipCycle p0 0 9 false (3) = true := by decide +kernel
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m :=
  zipCycle_sound p0 0 9 false (3) (by decide) cert0 m hm
#print axioms never0

/-- Raw45 first-hole depth 2, 1RB1LA_1RC0LA_0RD---_1LD1RB_------_------. -/
def p1 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert1 : zipCycle p1 8 3 false (0) = true := by decide +kernel
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m :=
  zipCycle_sound p1 8 3 false (0) (by decide) cert1 m hm
#print axioms never1

/-- Raw45 first-hole depth 2, 1RB0RA_1RC0LA_0RD---_1LD1RB_------_------. -/
def p2 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert2 : zipCycle p2 0 11 true (0) = true := by decide +kernel
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m :=
  zipCycle_sound p2 0 11 true (0) (by decide) cert2 m hm
#print axioms never2

/-- Raw45 first-hole depth 2, 1RB1RA_1RC0LA_0RD---_1LD1RB_------_------. -/
def p3 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert3 : zipCycle p3 0 11 true (0) = true := by decide +kernel
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m :=
  zipCycle_sound p3 0 11 true (0) (by decide) cert3 m hm
#print axioms never3

/-- Raw45 first-hole depth 2, 1RB0LB_1RC0LA_0RD---_1LD1RB_------_------. -/
def p4 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert4 : zipCycle p4 0 9 false (3) = true := by decide +kernel
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m :=
  zipCycle_sound p4 0 9 false (3) (by decide) cert4 m hm
#print axioms never4

/-- Raw45 first-hole depth 2, 1RB0RC_1RC0LA_0RD---_1LD1RB_------_------. -/
def p5 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert5 : zipCycle p5 1 9 true (1) = true := by decide +kernel
theorem never5 (m : Machine) (hm : compatible p5 m) : NeverHalts m :=
  zipCycle_sound p5 1 9 true (1) (by decide) cert5 m hm
#print axioms never5

/-- Raw45 first-hole depth 2, 1RB1RC_1RC0LA_0RD---_1LD1RB_------_------. -/
def p6 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert6 : zipCycle p6 1 9 true (1) = true := by decide +kernel
theorem never6 (m : Machine) (hm : compatible p6 m) : NeverHalts m :=
  zipCycle_sound p6 1 9 true (1) (by decide) cert6 m hm
#print axioms never6

/-- Raw45 first-hole depth 2, 1RB0LD_1RC0LA_0RD---_1LD1RB_------_------. -/
def p7 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert7 : zipCycle p7 1 11 true (0) = true := by decide +kernel
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m :=
  zipCycle_sound p7 1 11 true (0) (by decide) cert7 m hm
#print axioms never7

/-- Raw45 first-hole depth 2, 1RB1LD_1RC0LA_0RD---_1LD1RB_------_------. -/
def p8 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert8 : zipCycle p8 11 1 false (-1) = true := by decide +kernel
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m :=
  zipCycle_sound p8 11 1 false (-1) (by decide) cert8 m hm
#print axioms never8

/-- Raw45 first-hole depth 2, 1RB0RD_1RC0LA_0RD---_1LD1RB_------_------. -/
def p9 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert9 : zipCycle p9 13 1 false (1) = true := by decide +kernel
theorem never9 (m : Machine) (hm : compatible p9 m) : NeverHalts m :=
  zipCycle_sound p9 13 1 false (1) (by decide) cert9 m hm
#print axioms never9

/-- Raw45 first-hole depth 2, 1RB1RD_1RC0LA_0RD---_1LD1RB_------_------. -/
def p10 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert10 : zipCycle p10 4 4 true (1) = true := by decide +kernel
theorem never10 (m : Machine) (hm : compatible p10 m) : NeverHalts m :=
  zipCycle_sound p10 4 4 true (1) (by decide) cert10 m hm
#print axioms never10

/-- Raw45 first-hole depth 2, 1RB1LA_1RC1LA_0RD---_1LD1RB_------_------. -/
def p11 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert11 : zipCycle p11 8 3 false (0) = true := by decide +kernel
theorem never11 (m : Machine) (hm : compatible p11 m) : NeverHalts m :=
  zipCycle_sound p11 8 3 false (0) (by decide) cert11 m hm
#print axioms never11

/-- Raw45 first-hole depth 2, 1RB0RA_1RC1LA_0RD---_1LD1RB_------_------. -/
def p12 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert12 : zipCycle p12 0 10 true (0) = true := by decide +kernel
theorem never12 (m : Machine) (hm : compatible p12 m) : NeverHalts m :=
  zipCycle_sound p12 0 10 true (0) (by decide) cert12 m hm
#print axioms never12

/-- Raw45 first-hole depth 2, 1RB1RA_1RC1LA_0RD---_1LD1RB_------_------. -/
def p13 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert13 : zipCycle p13 0 10 true (0) = true := by decide +kernel
theorem never13 (m : Machine) (hm : compatible p13 m) : NeverHalts m :=
  zipCycle_sound p13 0 10 true (0) (by decide) cert13 m hm
#print axioms never13

/-- Raw45 first-hole depth 2, 1RB0RB_1RC1LA_0RD---_1LD1RB_------_------. -/
def p14 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert14 : zipCycle p14 6 4 true (1) = true := by decide +kernel
theorem never14 (m : Machine) (hm : compatible p14 m) : NeverHalts m :=
  zipCycle_sound p14 6 4 true (1) (by decide) cert14 m hm
#print axioms never14

/-- Raw45 first-hole depth 2, 1RB1RB_1RC1LA_0RD---_1LD1RB_------_------. -/
def p15 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert15 : zipCycle p15 6 2 true (1) = true := by decide +kernel
theorem never15 (m : Machine) (hm : compatible p15 m) : NeverHalts m :=
  zipCycle_sound p15 6 2 true (1) (by decide) cert15 m hm
#print axioms never15

/-- Raw45 first-hole depth 2, 1RB1LD_1RC1LA_0RD---_1LD1RB_------_------. -/
def p16 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert16 : zipCycle p16 11 1 false (-1) = true := by decide +kernel
theorem never16 (m : Machine) (hm : compatible p16 m) : NeverHalts m :=
  zipCycle_sound p16 11 1 false (-1) (by decide) cert16 m hm
#print axioms never16

/-- Raw45 first-hole depth 2, 1RB0RD_1RC1LA_0RD---_1LD1RB_------_------. -/
def p17 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert17 : zipCycle p17 1 11 true (1) = true := by decide +kernel
theorem never17 (m : Machine) (hm : compatible p17 m) : NeverHalts m :=
  zipCycle_sound p17 1 11 true (1) (by decide) cert17 m hm
#print axioms never17

/-- Raw45 first-hole depth 2, 1RB1RD_1RC1LA_0RD---_1LD1RB_------_------. -/
def p18 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert18 : zipCycle p18 1 11 true (1) = true := by decide +kernel
theorem never18 (m : Machine) (hm : compatible p18 m) : NeverHalts m :=
  zipCycle_sound p18 1 11 true (1) (by decide) cert18 m hm
#print axioms never18

/-- Raw45 first-hole depth 2, 1RB0LA_1RC0RA_0RD---_1LD1RB_------_------. -/
def p19 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert19 : zipCycle p19 0 8 true (0) = true := by decide +kernel
theorem never19 (m : Machine) (hm : compatible p19 m) : NeverHalts m :=
  zipCycle_sound p19 0 8 true (0) (by decide) cert19 m hm
#print axioms never19

/-- Raw45 first-hole depth 2, 1RB1LA_1RC0RA_0RD---_1LD1RB_------_------. -/
def p20 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert20 : zipCycle p20 0 10 true (0) = true := by decide +kernel
theorem never20 (m : Machine) (hm : compatible p20 m) : NeverHalts m :=
  zipCycle_sound p20 0 10 true (0) (by decide) cert20 m hm
#print axioms never20

/-- Raw45 first-hole depth 2, 1RB0RA_1RC0RA_0RD---_1LD1RB_------_------. -/
def p21 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert21 : zipCycle p21 0 8 true (0) = true := by decide +kernel
theorem never21 (m : Machine) (hm : compatible p21 m) : NeverHalts m :=
  zipCycle_sound p21 0 8 true (0) (by decide) cert21 m hm
#print axioms never21

/-- Raw45 first-hole depth 2, 1RB1RA_1RC0RA_0RD---_1LD1RB_------_------. -/
def p22 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert22 : zipCycle p22 0 8 true (0) = true := by decide +kernel
theorem never22 (m : Machine) (hm : compatible p22 m) : NeverHalts m :=
  zipCycle_sound p22 0 8 true (0) (by decide) cert22 m hm
#print axioms never22

/-- Raw45 first-hole depth 2, 1RB0LB_1RC0RA_0RD---_1LD1RB_------_------. -/
def p23 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert23 : zipCycle p23 1 7 true (1) = true := by decide +kernel
theorem never23 (m : Machine) (hm : compatible p23 m) : NeverHalts m :=
  zipCycle_sound p23 1 7 true (1) (by decide) cert23 m hm
#print axioms never23

/-- Raw45 first-hole depth 2, 1RB0RB_1RC0RA_0RD---_1LD1RB_------_------. -/
def p24 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert24 : zipCycle p24 1 7 true (1) = true := by decide +kernel
theorem never24 (m : Machine) (hm : compatible p24 m) : NeverHalts m :=
  zipCycle_sound p24 1 7 true (1) (by decide) cert24 m hm
#print axioms never24

/-- Raw45 first-hole depth 2, 1RB1RB_1RC0RA_0RD---_1LD1RB_------_------. -/
def p25 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert25 : zipCycle p25 1 7 true (1) = true := by decide +kernel
theorem never25 (m : Machine) (hm : compatible p25 m) : NeverHalts m :=
  zipCycle_sound p25 1 7 true (1) (by decide) cert25 m hm
#print axioms never25

/-- Raw45 first-hole depth 2, 1RB0LC_1RC0RA_0RD---_1LD1RB_------_------. -/
def p26 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert26 : zipCycle p26 2 6 true (1) = true := by decide +kernel
theorem never26 (m : Machine) (hm : compatible p26 m) : NeverHalts m :=
  zipCycle_sound p26 2 6 true (1) (by decide) cert26 m hm
#print axioms never26

/-- Raw45 first-hole depth 2, 1RB1LC_1RC0RA_0RD---_1LD1RB_------_------. -/
def p27 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert27 : zipCycle p27 1 9 true (1) = true := by decide +kernel
theorem never27 (m : Machine) (hm : compatible p27 m) : NeverHalts m :=
  zipCycle_sound p27 1 9 true (1) (by decide) cert27 m hm
#print axioms never27

/-- Raw45 first-hole depth 2, 1RB1RC_1RC0RA_0RD---_1LD1RB_------_------. -/
def p28 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert28 : zipCycle p28 2 6 true (1) = true := by decide +kernel
theorem never28 (m : Machine) (hm : compatible p28 m) : NeverHalts m :=
  zipCycle_sound p28 2 6 true (1) (by decide) cert28 m hm
#print axioms never28

/-- Raw45 first-hole depth 2, 1RB0LD_1RC0RA_0RD---_1LD1RB_------_------. -/
def p29 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert29 : zipCycle p29 0 11 true (0) = true := by decide +kernel
theorem never29 (m : Machine) (hm : compatible p29 m) : NeverHalts m :=
  zipCycle_sound p29 0 11 true (0) (by decide) cert29 m hm
#print axioms never29

/-- Raw45 first-hole depth 2, 1RB1LD_1RC0RA_0RD---_1LD1RB_------_------. -/
def p30 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert30 : zipCycle p30 4 4 true (1) = true := by decide +kernel
theorem never30 (m : Machine) (hm : compatible p30 m) : NeverHalts m :=
  zipCycle_sound p30 4 4 true (1) (by decide) cert30 m hm
#print axioms never30

/-- Raw45 first-hole depth 2, 1RB0RD_1RC0RA_0RD---_1LD1RB_------_------. -/
def p31 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert31 : zipCycle p31 1 14 true (1) = true := by decide +kernel
theorem never31 (m : Machine) (hm : compatible p31 m) : NeverHalts m :=
  zipCycle_sound p31 1 14 true (1) (by decide) cert31 m hm
#print axioms never31

/-- Raw45 first-hole depth 2, 1RB1RD_1RC0RA_0RD---_1LD1RB_------_------. -/
def p32 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert32 : zipCycle p32 0 11 true (0) = true := by decide +kernel
theorem never32 (m : Machine) (hm : compatible p32 m) : NeverHalts m :=
  zipCycle_sound p32 0 11 true (0) (by decide) cert32 m hm
#print axioms never32

/-- Raw45 first-hole depth 2, 1RB0LA_1RC1RA_0RD---_1LD1RB_------_------. -/
def p33 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert33 : zipCycle p33 0 11 false (3) = true := by decide +kernel
theorem never33 (m : Machine) (hm : compatible p33 m) : NeverHalts m :=
  zipCycle_sound p33 0 11 false (3) (by decide) cert33 m hm
#print axioms never33

/-- Raw45 first-hole depth 2, 1RB1LA_1RC1RA_0RD---_1LD1RB_------_------. -/
def p34 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert34 : zipCycle p34 8 5 false (2) = true := by decide +kernel
theorem never34 (m : Machine) (hm : compatible p34 m) : NeverHalts m :=
  zipCycle_sound p34 8 5 false (2) (by decide) cert34 m hm
#print axioms never34

/-- Raw45 first-hole depth 2, 1RB0RA_1RC1RA_0RD---_1LD1RB_------_------. -/
def p35 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert35 : zipCycle p35 0 8 true (0) = true := by decide +kernel
theorem never35 (m : Machine) (hm : compatible p35 m) : NeverHalts m :=
  zipCycle_sound p35 0 8 true (0) (by decide) cert35 m hm
#print axioms never35

/-- Raw45 first-hole depth 2, 1RB1RA_1RC1RA_0RD---_1LD1RB_------_------. -/
def p36 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert36 : zipCycle p36 0 8 true (0) = true := by decide +kernel
theorem never36 (m : Machine) (hm : compatible p36 m) : NeverHalts m :=
  zipCycle_sound p36 0 8 true (0) (by decide) cert36 m hm
#print axioms never36

/-- Raw45 first-hole depth 2, 1RB0LB_1RC1RA_0RD---_1LD1RB_------_------. -/
def p37 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert37 : zipCycle p37 0 9 true (0) = true := by decide +kernel
theorem never37 (m : Machine) (hm : compatible p37 m) : NeverHalts m :=
  zipCycle_sound p37 0 9 true (0) (by decide) cert37 m hm
#print axioms never37

/-- Raw45 first-hole depth 2, 1RB1LB_1RC1RA_0RD---_1LD1RB_------_------. -/
def p38 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert38 : zipCycle p38 6 2 true (2) = true := by decide +kernel
theorem never38 (m : Machine) (hm : compatible p38 m) : NeverHalts m :=
  zipCycle_sound p38 6 2 true (2) (by decide) cert38 m hm
#print axioms never38

/-- Raw45 first-hole depth 2, 1RB0RB_1RC1RA_0RD---_1LD1RB_------_------. -/
def p39 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert39 : zipCycle p39 1 7 true (1) = true := by decide +kernel
theorem never39 (m : Machine) (hm : compatible p39 m) : NeverHalts m :=
  zipCycle_sound p39 1 7 true (1) (by decide) cert39 m hm
#print axioms never39
end BB6.Agent24Raw45D2A
