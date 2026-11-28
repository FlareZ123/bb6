import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D2C
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD0LD_1LD1RB_------_------. -/
def p80 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert80 : zipCycle p80 1 14 true (0) = true := by decide +kernel
theorem never80 (m : Machine) (hm : compatible p80 m) : NeverHalts m :=
  zipCycle_sound p80 1 14 true (0) (by decide) cert80 m hm
#print axioms never80

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD1LD_1LD1RB_------_------. -/
def p81 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert81 : zipCycle p81 11 1 false (-1) = true := by decide +kernel
theorem never81 (m : Machine) (hm : compatible p81 m) : NeverHalts m :=
  zipCycle_sound p81 11 1 false (-1) (by decide) cert81 m hm
#print axioms never81

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD0RD_1LD1RB_------_------. -/
def p82 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert82 : zipCycle p82 1 11 true (1) = true := by decide +kernel
theorem never82 (m : Machine) (hm : compatible p82 m) : NeverHalts m :=
  zipCycle_sound p82 1 11 true (1) (by decide) cert82 m hm
#print axioms never82

/-- Raw45 first-hole depth 2, 1RB---_1RC1LC_0RD1RD_1LD1RB_------_------. -/
def p83 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert83 : zipCycle p83 1 11 true (1) = true := by decide +kernel
theorem never83 (m : Machine) (hm : compatible p83 m) : NeverHalts m :=
  zipCycle_sound p83 1 11 true (1) (by decide) cert83 m hm
#print axioms never83

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0LA_1LD1RB_------_------. -/
def p84 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert84 : zipCycle p84 0 8 true (0) = true := by decide +kernel
theorem never84 (m : Machine) (hm : compatible p84 m) : NeverHalts m :=
  zipCycle_sound p84 0 8 true (0) (by decide) cert84 m hm
#print axioms never84

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1LA_1LD1RB_------_------. -/
def p85 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert85 : zipCycle p85 6 12 true (2) = true := by decide +kernel
theorem never85 (m : Machine) (hm : compatible p85 m) : NeverHalts m :=
  zipCycle_sound p85 6 12 true (2) (by decide) cert85 m hm
#print axioms never85

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0RA_1LD1RB_------_------. -/
def p86 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert86 : zipCycle p86 0 8 true (0) = true := by decide +kernel
theorem never86 (m : Machine) (hm : compatible p86 m) : NeverHalts m :=
  zipCycle_sound p86 0 8 true (0) (by decide) cert86 m hm
#print axioms never86

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1RA_1LD1RB_------_------. -/
def p87 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert87 : zipCycle p87 0 8 true (0) = true := by decide +kernel
theorem never87 (m : Machine) (hm : compatible p87 m) : NeverHalts m :=
  zipCycle_sound p87 0 8 true (0) (by decide) cert87 m hm
#print axioms never87

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0LB_1LD1RB_------_------. -/
def p88 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert88 : zipCycle p88 1 7 true (1) = true := by decide +kernel
theorem never88 (m : Machine) (hm : compatible p88 m) : NeverHalts m :=
  zipCycle_sound p88 1 7 true (1) (by decide) cert88 m hm
#print axioms never88

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1LB_1LD1RB_------_------. -/
def p89 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert89 : zipCycle p89 6 4 true (2) = true := by decide +kernel
theorem never89 (m : Machine) (hm : compatible p89 m) : NeverHalts m :=
  zipCycle_sound p89 6 4 true (2) (by decide) cert89 m hm
#print axioms never89

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0RB_1LD1RB_------_------. -/
def p90 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert90 : zipCycle p90 1 7 true (1) = true := by decide +kernel
theorem never90 (m : Machine) (hm : compatible p90 m) : NeverHalts m :=
  zipCycle_sound p90 1 7 true (1) (by decide) cert90 m hm
#print axioms never90

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1RB_1LD1RB_------_------. -/
def p91 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert91 : zipCycle p91 1 7 true (1) = true := by decide +kernel
theorem never91 (m : Machine) (hm : compatible p91 m) : NeverHalts m :=
  zipCycle_sound p91 1 7 true (1) (by decide) cert91 m hm
#print axioms never91

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0LC_1LD1RB_------_------. -/
def p92 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert92 : zipCycle p92 2 6 true (1) = true := by decide +kernel
theorem never92 (m : Machine) (hm : compatible p92 m) : NeverHalts m :=
  zipCycle_sound p92 2 6 true (1) (by decide) cert92 m hm
#print axioms never92

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1LC_1LD1RB_------_------. -/
def p93 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert93 : zipCycle p93 1 9 true (1) = true := by decide +kernel
theorem never93 (m : Machine) (hm : compatible p93 m) : NeverHalts m :=
  zipCycle_sound p93 1 9 true (1) (by decide) cert93 m hm
#print axioms never93

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1RC_1LD1RB_------_------. -/
def p94 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert94 : zipCycle p94 2 6 true (1) = true := by decide +kernel
theorem never94 (m : Machine) (hm : compatible p94 m) : NeverHalts m :=
  zipCycle_sound p94 2 6 true (1) (by decide) cert94 m hm
#print axioms never94

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0LD_1LD1RB_------_------. -/
def p95 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert95 : zipCycle p95 1 22 true (1) = true := by decide +kernel
theorem never95 (m : Machine) (hm : compatible p95 m) : NeverHalts m :=
  zipCycle_sound p95 1 22 true (1) (by decide) cert95 m hm
#print axioms never95

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1LD_1LD1RB_------_------. -/
def p96 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert96 : zipCycle p96 4 4 true (1) = true := by decide +kernel
theorem never96 (m : Machine) (hm : compatible p96 m) : NeverHalts m :=
  zipCycle_sound p96 4 4 true (1) (by decide) cert96 m hm
#print axioms never96

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD0RD_1LD1RB_------_------. -/
def p97 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert97 : zipCycle p97 1 14 true (1) = true := by decide +kernel
theorem never97 (m : Machine) (hm : compatible p97 m) : NeverHalts m :=
  zipCycle_sound p97 1 14 true (1) (by decide) cert97 m hm
#print axioms never97

/-- Raw45 first-hole depth 2, 1RB---_1RC0RC_0RD1RD_1LD1RB_------_------. -/
def p98 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert98 : zipCycle p98 1 18 true (1) = true := by decide +kernel
theorem never98 (m : Machine) (hm : compatible p98 m) : NeverHalts m :=
  zipCycle_sound p98 1 18 true (1) (by decide) cert98 m hm
#print axioms never98

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD0RA_1LD1RB_------_------. -/
def p99 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert99 : zipCycle p99 0 8 true (0) = true := by decide +kernel
theorem never99 (m : Machine) (hm : compatible p99 m) : NeverHalts m :=
  zipCycle_sound p99 0 8 true (0) (by decide) cert99 m hm
#print axioms never99

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1RA_1LD1RB_------_------. -/
def p100 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert100 : zipCycle p100 0 8 true (0) = true := by decide +kernel
theorem never100 (m : Machine) (hm : compatible p100 m) : NeverHalts m :=
  zipCycle_sound p100 0 8 true (0) (by decide) cert100 m hm
#print axioms never100

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD0LB_1LD1RB_------_------. -/
def p101 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert101 : zipCycle p101 2 7 true (1) = true := by decide +kernel
theorem never101 (m : Machine) (hm : compatible p101 m) : NeverHalts m :=
  zipCycle_sound p101 2 7 true (1) (by decide) cert101 m hm
#print axioms never101

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1LB_1LD1RB_------_------. -/
def p102 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert102 : zipCycle p102 6 2 true (2) = true := by decide +kernel
theorem never102 (m : Machine) (hm : compatible p102 m) : NeverHalts m :=
  zipCycle_sound p102 6 2 true (2) (by decide) cert102 m hm
#print axioms never102

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD0RB_1LD1RB_------_------. -/
def p103 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert103 : zipCycle p103 1 7 true (1) = true := by decide +kernel
theorem never103 (m : Machine) (hm : compatible p103 m) : NeverHalts m :=
  zipCycle_sound p103 1 7 true (1) (by decide) cert103 m hm
#print axioms never103

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1RB_1LD1RB_------_------. -/
def p104 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert104 : zipCycle p104 1 7 true (1) = true := by decide +kernel
theorem never104 (m : Machine) (hm : compatible p104 m) : NeverHalts m :=
  zipCycle_sound p104 1 7 true (1) (by decide) cert104 m hm
#print axioms never104

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD0LC_1LD1RB_------_------. -/
def p105 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert105 : zipCycle p105 12 1 false (0) = true := by decide +kernel
theorem never105 (m : Machine) (hm : compatible p105 m) : NeverHalts m :=
  zipCycle_sound p105 12 1 false (0) (by decide) cert105 m hm
#print axioms never105

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1LC_1LD1RB_------_------. -/
def p106 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert106 : zipCycle p106 8 6 true (-1) = true := by decide +kernel
theorem never106 (m : Machine) (hm : compatible p106 m) : NeverHalts m :=
  zipCycle_sound p106 8 6 true (-1) (by decide) cert106 m hm
#print axioms never106

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1RC_1LD1RB_------_------. -/
def p107 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert107 : zipCycle p107 2 6 true (1) = true := by decide +kernel
theorem never107 (m : Machine) (hm : compatible p107 m) : NeverHalts m :=
  zipCycle_sound p107 2 6 true (1) (by decide) cert107 m hm
#print axioms never107

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD0LD_1LD1RB_------_------. -/
def p108 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert108 : zipCycle p108 1 8 true (1) = true := by decide +kernel
theorem never108 (m : Machine) (hm : compatible p108 m) : NeverHalts m :=
  zipCycle_sound p108 1 8 true (1) (by decide) cert108 m hm
#print axioms never108

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1LD_1LD1RB_------_------. -/
def p109 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert109 : zipCycle p109 2 8 true (1) = true := by decide +kernel
theorem never109 (m : Machine) (hm : compatible p109 m) : NeverHalts m :=
  zipCycle_sound p109 2 8 true (1) (by decide) cert109 m hm
#print axioms never109

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD0RD_1LD1RB_------_------. -/
def p110 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert110 : zipCycle p110 3 5 true (1) = true := by decide +kernel
theorem never110 (m : Machine) (hm : compatible p110 m) : NeverHalts m :=
  zipCycle_sound p110 3 5 true (1) (by decide) cert110 m hm
#print axioms never110

/-- Raw45 first-hole depth 2, 1RB---_1RC1RC_0RD1RD_1LD1RB_------_------. -/
def p111 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert111 : zipCycle p111 2 9 true (1) = true := by decide +kernel
theorem never111 (m : Machine) (hm : compatible p111 m) : NeverHalts m :=
  zipCycle_sound p111 2 9 true (1) (by decide) cert111 m hm
#print axioms never111

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD0RA_1LD1RB_------_------. -/
def p112 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert112 : zipCycle p112 0 10 true (0) = true := by decide +kernel
theorem never112 (m : Machine) (hm : compatible p112 m) : NeverHalts m :=
  zipCycle_sound p112 0 10 true (0) (by decide) cert112 m hm
#print axioms never112

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1RA_1LD1RB_------_------. -/
def p113 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert113 : zipCycle p113 0 10 true (0) = true := by decide +kernel
theorem never113 (m : Machine) (hm : compatible p113 m) : NeverHalts m :=
  zipCycle_sound p113 0 10 true (0) (by decide) cert113 m hm
#print axioms never113

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD0LB_1LD1RB_------_------. -/
def p114 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert114 : zipCycle p114 1 11 true (1) = true := by decide +kernel
theorem never114 (m : Machine) (hm : compatible p114 m) : NeverHalts m :=
  zipCycle_sound p114 1 11 true (1) (by decide) cert114 m hm
#print axioms never114

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1LB_1LD1RB_------_------. -/
def p115 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert115 : zipCycle p115 6 4 true (1) = true := by decide +kernel
theorem never115 (m : Machine) (hm : compatible p115 m) : NeverHalts m :=
  zipCycle_sound p115 6 4 true (1) (by decide) cert115 m hm
#print axioms never115

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD0RB_1LD1RB_------_------. -/
def p116 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert116 : zipCycle p116 1 9 true (1) = true := by decide +kernel
theorem never116 (m : Machine) (hm : compatible p116 m) : NeverHalts m :=
  zipCycle_sound p116 1 9 true (1) (by decide) cert116 m hm
#print axioms never116

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1RB_1LD1RB_------_------. -/
def p117 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert117 : zipCycle p117 1 9 true (1) = true := by decide +kernel
theorem never117 (m : Machine) (hm : compatible p117 m) : NeverHalts m :=
  zipCycle_sound p117 1 9 true (1) (by decide) cert117 m hm
#print axioms never117

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD0LC_1LD1RB_------_------. -/
def p118 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert118 : zipCycle p118 14 1 false (0) = true := by decide +kernel
theorem never118 (m : Machine) (hm : compatible p118 m) : NeverHalts m :=
  zipCycle_sound p118 14 1 false (0) (by decide) cert118 m hm
#print axioms never118

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1LC_1LD1RB_------_------. -/
def p119 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert119 : zipCycle p119 10 8 true (-1) = true := by decide +kernel
theorem never119 (m : Machine) (hm : compatible p119 m) : NeverHalts m :=
  zipCycle_sound p119 10 8 true (-1) (by decide) cert119 m hm
#print axioms never119
end BB6.Agent24Raw45D2C
