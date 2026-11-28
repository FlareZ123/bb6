import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D2B
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Raw45 first-hole depth 2, 1RB1RB_1RC1RA_0RD---_1LD1RB_------_------. -/
def p40 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert40 : zipCycle p40 1 7 true (1) = true := by decide +kernel
theorem never40 (m : Machine) (hm : compatible p40 m) : NeverHalts m :=
  zipCycle_sound p40 1 7 true (1) (by decide) cert40 m hm
#print axioms never40

/-- Raw45 first-hole depth 2, 1RB1RC_1RC1RA_0RD---_1LD1RB_------_------. -/
def p41 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert41 : zipCycle p41 2 6 true (1) = true := by decide +kernel
theorem never41 (m : Machine) (hm : compatible p41 m) : NeverHalts m :=
  zipCycle_sound p41 2 6 true (1) (by decide) cert41 m hm
#print axioms never41

/-- Raw45 first-hole depth 2, 1RB0LD_1RC1RA_0RD---_1LD1RB_------_------. -/
def p42 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert42 : zipCycle p42 1 8 true (1) = true := by decide +kernel
theorem never42 (m : Machine) (hm : compatible p42 m) : NeverHalts m :=
  zipCycle_sound p42 1 8 true (1) (by decide) cert42 m hm
#print axioms never42

/-- Raw45 first-hole depth 2, 1RB1LD_1RC1RA_0RD---_1LD1RB_------_------. -/
def p43 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert43 : zipCycle p43 0 10 true (0) = true := by decide +kernel
theorem never43 (m : Machine) (hm : compatible p43 m) : NeverHalts m :=
  zipCycle_sound p43 0 10 true (0) (by decide) cert43 m hm
#print axioms never43

/-- Raw45 first-hole depth 2, 1RB0RD_1RC1RA_0RD---_1LD1RB_------_------. -/
def p44 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert44 : zipCycle p44 3 5 true (1) = true := by decide +kernel
theorem never44 (m : Machine) (hm : compatible p44 m) : NeverHalts m :=
  zipCycle_sound p44 3 5 true (1) (by decide) cert44 m hm
#print axioms never44

/-- Raw45 first-hole depth 2, 1RB1RD_1RC1RA_0RD---_1LD1RB_------_------. -/
def p45 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert45 : zipCycle p45 0 11 true (0) = true := by decide +kernel
theorem never45 (m : Machine) (hm : compatible p45 m) : NeverHalts m :=
  zipCycle_sound p45 0 11 true (0) (by decide) cert45 m hm
#print axioms never45

/-- Raw45 first-hole depth 1, 1RB---_1RC0LB_0RD---_1LD1RB_------_------. -/
def p46 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert46 : zipCycle p46 7 7 false (1) = true := by decide +kernel
theorem never46 (m : Machine) (hm : compatible p46 m) : NeverHalts m :=
  zipCycle_sound p46 7 7 false (1) (by decide) cert46 m hm
#print axioms never46

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD0LB_1LD1RB_------_------. -/
def p47 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert47 : zipCycle p47 8 3 false (0) = true := by decide +kernel
theorem never47 (m : Machine) (hm : compatible p47 m) : NeverHalts m :=
  zipCycle_sound p47 8 3 false (0) (by decide) cert47 m hm
#print axioms never47

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD1LB_1LD1RB_------_------. -/
def p48 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert48 : zipCycle p48 8 3 false (0) = true := by decide +kernel
theorem never48 (m : Machine) (hm : compatible p48 m) : NeverHalts m :=
  zipCycle_sound p48 8 3 false (0) (by decide) cert48 m hm
#print axioms never48

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD0RB_1LD1RB_------_------. -/
def p49 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert49 : zipCycle p49 11 15 true (0) = true := by decide +kernel
theorem never49 (m : Machine) (hm : compatible p49 m) : NeverHalts m :=
  zipCycle_sound p49 11 15 true (0) (by decide) cert49 m hm
#print axioms never49

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD1RB_1LD1RB_------_------. -/
def p50 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert50 : zipCycle p50 6 5 false (2) = true := by decide +kernel
theorem never50 (m : Machine) (hm : compatible p50 m) : NeverHalts m :=
  zipCycle_sound p50 6 5 false (2) (by decide) cert50 m hm
#print axioms never50

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD0LC_1LD1RB_------_------. -/
def p51 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert51 : zipCycle p51 13 1 false (-1) = true := by decide +kernel
theorem never51 (m : Machine) (hm : compatible p51 m) : NeverHalts m :=
  zipCycle_sound p51 13 1 false (-1) (by decide) cert51 m hm
#print axioms never51

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD1LC_1LD1RB_------_------. -/
def p52 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert52 : zipCycle p52 7 7 false (1) = true := by decide +kernel
theorem never52 (m : Machine) (hm : compatible p52 m) : NeverHalts m :=
  zipCycle_sound p52 7 7 false (1) (by decide) cert52 m hm
#print axioms never52

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD1LD_1LD1RB_------_------. -/
def p53 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert53 : zipCycle p53 7 5 false (1) = true := by decide +kernel
theorem never53 (m : Machine) (hm : compatible p53 m) : NeverHalts m :=
  zipCycle_sound p53 7 5 false (1) (by decide) cert53 m hm
#print axioms never53

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD0RD_1LD1RB_------_------. -/
def p54 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert54 : zipCycle p54 1 21 true (-1) = true := by decide +kernel
theorem never54 (m : Machine) (hm : compatible p54 m) : NeverHalts m :=
  zipCycle_sound p54 1 21 true (-1) (by decide) cert54 m hm
#print axioms never54

/-- Raw45 first-hole depth 2, 1RB---_1RC1LB_0RD1RD_1LD1RB_------_------. -/
def p55 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert55 : zipCycle p55 6 7 false (2) = true := by decide +kernel
theorem never55 (m : Machine) (hm : compatible p55 m) : NeverHalts m :=
  zipCycle_sound p55 6 7 false (2) (by decide) cert55 m hm
#print axioms never55

/-- Raw45 first-hole depth 1, 1RB---_1RC0RB_0RD---_1LD1RB_------_------. -/
def p56 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert56 : zipCycle p56 1 7 true (1) = true := by decide +kernel
theorem never56 (m : Machine) (hm : compatible p56 m) : NeverHalts m :=
  zipCycle_sound p56 1 7 true (1) (by decide) cert56 m hm
#print axioms never56

/-- Raw45 first-hole depth 1, 1RB---_1RC1RB_0RD---_1LD1RB_------_------. -/
def p57 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,1⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert57 : zipCycle p57 1 7 true (1) = true := by decide +kernel
theorem never57 (m : Machine) (hm : compatible p57 m) : NeverHalts m :=
  zipCycle_sound p57 1 7 true (1) (by decide) cert57 m hm
#print axioms never57

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0RA_1LD1RB_------_------. -/
def p58 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert58 : zipCycle p58 0 11 true (0) = true := by decide +kernel
theorem never58 (m : Machine) (hm : compatible p58 m) : NeverHalts m :=
  zipCycle_sound p58 0 11 true (0) (by decide) cert58 m hm
#print axioms never58

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1RA_1LD1RB_------_------. -/
def p59 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert59 : zipCycle p59 0 11 true (0) = true := by decide +kernel
theorem never59 (m : Machine) (hm : compatible p59 m) : NeverHalts m :=
  zipCycle_sound p59 0 11 true (0) (by decide) cert59 m hm
#print axioms never59

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0LB_1LD1RB_------_------. -/
def p60 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert60 : zipCycle p60 10 1 false (0) = true := by decide +kernel
theorem never60 (m : Machine) (hm : compatible p60 m) : NeverHalts m :=
  zipCycle_sound p60 10 1 false (0) (by decide) cert60 m hm
#print axioms never60

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1LB_1LD1RB_------_------. -/
def p61 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert61 : zipCycle p61 10 1 false (0) = true := by decide +kernel
theorem never61 (m : Machine) (hm : compatible p61 m) : NeverHalts m :=
  zipCycle_sound p61 10 1 false (0) (by decide) cert61 m hm
#print axioms never61

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0RB_1LD1RB_------_------. -/
def p62 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert62 : zipCycle p62 1 9 true (1) = true := by decide +kernel
theorem never62 (m : Machine) (hm : compatible p62 m) : NeverHalts m :=
  zipCycle_sound p62 1 9 true (1) (by decide) cert62 m hm
#print axioms never62

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1RB_1LD1RB_------_------. -/
def p63 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert63 : zipCycle p63 1 9 true (1) = true := by decide +kernel
theorem never63 (m : Machine) (hm : compatible p63 m) : NeverHalts m :=
  zipCycle_sound p63 1 9 true (1) (by decide) cert63 m hm
#print axioms never63

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0LC_1LD1RB_------_------. -/
def p64 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert64 : zipCycle p64 10 1 false (0) = true := by decide +kernel
theorem never64 (m : Machine) (hm : compatible p64 m) : NeverHalts m :=
  zipCycle_sound p64 10 1 false (0) (by decide) cert64 m hm
#print axioms never64

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1LC_1LD1RB_------_------. -/
def p65 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert65 : zipCycle p65 1 17 true (-1) = true := by decide +kernel
theorem never65 (m : Machine) (hm : compatible p65 m) : NeverHalts m :=
  zipCycle_sound p65 1 17 true (-1) (by decide) cert65 m hm
#print axioms never65

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0RC_1LD1RB_------_------. -/
def p66 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert66 : zipCycle p66 1 9 true (1) = true := by decide +kernel
theorem never66 (m : Machine) (hm : compatible p66 m) : NeverHalts m :=
  zipCycle_sound p66 1 9 true (1) (by decide) cert66 m hm
#print axioms never66

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1RC_1LD1RB_------_------. -/
def p67 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert67 : zipCycle p67 1 9 true (1) = true := by decide +kernel
theorem never67 (m : Machine) (hm : compatible p67 m) : NeverHalts m :=
  zipCycle_sound p67 1 9 true (1) (by decide) cert67 m hm
#print axioms never67

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0LD_1LD1RB_------_------. -/
def p68 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert68 : zipCycle p68 1 11 true (0) = true := by decide +kernel
theorem never68 (m : Machine) (hm : compatible p68 m) : NeverHalts m :=
  zipCycle_sound p68 1 11 true (0) (by decide) cert68 m hm
#print axioms never68

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1LD_1LD1RB_------_------. -/
def p69 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert69 : zipCycle p69 11 1 false (-1) = true := by decide +kernel
theorem never69 (m : Machine) (hm : compatible p69 m) : NeverHalts m :=
  zipCycle_sound p69 11 1 false (-1) (by decide) cert69 m hm
#print axioms never69

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD0RD_1LD1RB_------_------. -/
def p70 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert70 : zipCycle p70 13 1 false (1) = true := by decide +kernel
theorem never70 (m : Machine) (hm : compatible p70 m) : NeverHalts m :=
  zipCycle_sound p70 13 1 false (1) (by decide) cert70 m hm
#print axioms never70

/-- Raw45 first-hole depth 2, 1RB---_1RC0LC_0RD1RD_1LD1RB_------_------. -/
def p71 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert71 : zipCycle p71 4 4 true (1) = true := by decide +kernel
theorem never71 (m : Machine) (hm : compatible p71 m) : NeverHalts m :=
  zipCycle_sound p71 4 4 true (1) (by decide) cert71 m hm
#print axioms never71

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD0LB_1LD1RB_------_------. -/
def p72 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert72 : zipCycle p72 1 24 true (-1) = true := by decide +kernel
theorem never72 (m : Machine) (hm : compatible p72 m) : NeverHalts m :=
  zipCycle_sound p72 1 24 true (-1) (by decide) cert72 m hm
#print axioms never72

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD1LB_1LD1RB_------_------. -/
def p73 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert73 : zipCycle p73 7 7 false (1) = true := by decide +kernel
theorem never73 (m : Machine) (hm : compatible p73 m) : NeverHalts m :=
  zipCycle_sound p73 7 7 false (1) (by decide) cert73 m hm
#print axioms never73

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD0RB_1LD1RB_------_------. -/
def p74 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert74 : zipCycle p74 1 15 true (1) = true := by decide +kernel
theorem never74 (m : Machine) (hm : compatible p74 m) : NeverHalts m :=
  zipCycle_sound p74 1 15 true (1) (by decide) cert74 m hm
#print axioms never74

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD1RB_1LD1RB_------_------. -/
def p75 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert75 : zipCycle p75 6 2 true (1) = true := by decide +kernel
theorem never75 (m : Machine) (hm : compatible p75 m) : NeverHalts m :=
  zipCycle_sound p75 6 2 true (1) (by decide) cert75 m hm
#print axioms never75

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD0LC_1LD1RB_------_------. -/
def p76 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert76 : zipCycle p76 10 1 false (0) = true := by decide +kernel
theorem never76 (m : Machine) (hm : compatible p76 m) : NeverHalts m :=
  zipCycle_sound p76 10 1 false (0) (by decide) cert76 m hm
#print axioms never76

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD1LC_1LD1RB_------_------. -/
def p77 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert77 : zipCycle p77 8 4 true (-1) = true := by decide +kernel
theorem never77 (m : Machine) (hm : compatible p77 m) : NeverHalts m :=
  zipCycle_sound p77 8 4 true (-1) (by decide) cert77 m hm
#print axioms never77

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD0RC_1LD1RB_------_------. -/
def p78 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert78 : zipCycle p78 25 1 false (7) = true := by decide +kernel
theorem never78 (m : Machine) (hm : compatible p78 m) : NeverHalts m :=
  zipCycle_sound p78 25 1 false (7) (by decide) cert78 m hm
#print axioms never78

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD1RC_1LD1RB_------_------. -/
def p79 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert79 : zipCycle p79 2 8 true (1) = true := by decide +kernel
theorem never79 (m : Machine) (hm : compatible p79 m) : NeverHalts m :=
  zipCycle_sound p79 2 8 true (1) (by decide) cert79 m hm
#print axioms never79
end BB6.Agent24Raw45D2B
