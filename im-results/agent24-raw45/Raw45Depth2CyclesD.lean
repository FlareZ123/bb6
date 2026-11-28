import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D2D
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1RC_1LD1RB_------_------. -/
def p120 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert120 : zipCycle p120 2 8 true (1) = true := by decide +kernel
theorem never120 (m : Machine) (hm : compatible p120 m) : NeverHalts m :=
  zipCycle_sound p120 2 8 true (1) (by decide) cert120 m hm
#print axioms never120

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD0LD_1LD1RB_------_------. -/
def p121 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert121 : zipCycle p121 1 10 true (1) = true := by decide +kernel
theorem never121 (m : Machine) (hm : compatible p121 m) : NeverHalts m :=
  zipCycle_sound p121 1 10 true (1) (by decide) cert121 m hm
#print axioms never121

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1LD_1LD1RB_------_------. -/
def p122 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert122 : zipCycle p122 1 12 true (1) = true := by decide +kernel
theorem never122 (m : Machine) (hm : compatible p122 m) : NeverHalts m :=
  zipCycle_sound p122 1 12 true (1) (by decide) cert122 m hm
#print axioms never122

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD0RD_1LD1RB_------_------. -/
def p123 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert123 : zipCycle p123 3 7 true (1) = true := by decide +kernel
theorem never123 (m : Machine) (hm : compatible p123 m) : NeverHalts m :=
  zipCycle_sound p123 3 7 true (1) (by decide) cert123 m hm
#print axioms never123

/-- Raw45 first-hole depth 2, 1RB---_1RC0LD_0RD1RD_1LD1RB_------_------. -/
def p124 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert124 : zipCycle p124 1 13 true (1) = true := by decide +kernel
theorem never124 (m : Machine) (hm : compatible p124 m) : NeverHalts m :=
  zipCycle_sound p124 1 13 true (1) (by decide) cert124 m hm
#print axioms never124

/-- Raw45 first-hole depth 1, 1RB---_1RC1LD_0RD---_1LD1RB_------_------. -/
def p125 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert125 : zipCycle p125 5 2 true (1) = true := by decide +kernel
theorem never125 (m : Machine) (hm : compatible p125 m) : NeverHalts m :=
  zipCycle_sound p125 5 2 true (1) (by decide) cert125 m hm
#print axioms never125

/-- Raw45 first-hole depth 1, 1RB---_1RC0RD_0RD---_1LD1RB_------_------. -/
def p126 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert126 : zipCycle p126 1 7 true (1) = true := by decide +kernel
theorem never126 (m : Machine) (hm : compatible p126 m) : NeverHalts m :=
  zipCycle_sound p126 1 7 true (1) (by decide) cert126 m hm
#print axioms never126

/-- Raw45 first-hole depth 1, 1RB---_1RC1RD_0RD---_1LD1RB_------_------. -/
def p127 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert127 : zipCycle p127 1 7 true (1) = true := by decide +kernel
theorem never127 (m : Machine) (hm : compatible p127 m) : NeverHalts m :=
  zipCycle_sound p127 1 7 true (1) (by decide) cert127 m hm
#print axioms never127

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---0RA_------. -/
def p128 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none

theorem cert128 : zipCycle p128 0 11 true (0) = true := by decide +kernel
theorem never128 (m : Machine) (hm : compatible p128 m) : NeverHalts m :=
  zipCycle_sound p128 0 11 true (0) (by decide) cert128 m hm
#print axioms never128

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---1RA_------. -/
def p129 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem cert129 : zipCycle p129 0 11 true (0) = true := by decide +kernel
theorem never129 (m : Machine) (hm : compatible p129 m) : NeverHalts m :=
  zipCycle_sound p129 0 11 true (0) (by decide) cert129 m hm
#print axioms never129

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---0RC_------. -/
def p130 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none

theorem cert130 : zipCycle p130 1 9 true (1) = true := by decide +kernel
theorem never130 (m : Machine) (hm : compatible p130 m) : NeverHalts m :=
  zipCycle_sound p130 1 9 true (1) (by decide) cert130 m hm
#print axioms never130

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---1RC_------. -/
def p131 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none

theorem cert131 : zipCycle p131 1 9 true (1) = true := by decide +kernel
theorem never131 (m : Machine) (hm : compatible p131 m) : NeverHalts m :=
  zipCycle_sound p131 1 9 true (1) (by decide) cert131 m hm
#print axioms never131

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---0LD_------. -/
def p132 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none

theorem cert132 : zipCycle p132 1 11 true (0) = true := by decide +kernel
theorem never132 (m : Machine) (hm : compatible p132 m) : NeverHalts m :=
  zipCycle_sound p132 1 11 true (0) (by decide) cert132 m hm
#print axioms never132

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---1LD_------. -/
def p133 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none

theorem cert133 : zipCycle p133 11 1 false (-1) = true := by decide +kernel
theorem never133 (m : Machine) (hm : compatible p133 m) : NeverHalts m :=
  zipCycle_sound p133 11 1 false (-1) (by decide) cert133 m hm
#print axioms never133

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---0RD_------. -/
def p134 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none

theorem cert134 : zipCycle p134 13 1 false (1) = true := by decide +kernel
theorem never134 (m : Machine) (hm : compatible p134 m) : NeverHalts m :=
  zipCycle_sound p134 13 1 false (1) (by decide) cert134 m hm
#print axioms never134

/-- Raw45 first-hole depth 2, 1RB---_1RC0LE_0RD---_1LD1RB_---1RD_------. -/
def p135 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none

theorem cert135 : zipCycle p135 4 4 true (1) = true := by decide +kernel
theorem never135 (m : Machine) (hm : compatible p135 m) : NeverHalts m :=
  zipCycle_sound p135 4 4 true (1) (by decide) cert135 m hm
#print axioms never135

/-- Raw45 first-hole depth 2, 1RB---_1RC1LE_0RD---_1LD1RB_---1RB_------. -/
def p136 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert136 : zipCycle p136 6 2 true (1) = true := by decide +kernel
theorem never136 (m : Machine) (hm : compatible p136 m) : NeverHalts m :=
  zipCycle_sound p136 6 2 true (1) (by decide) cert136 m hm
#print axioms never136

/-- Raw45 first-hole depth 2, 1RB---_1RC1LE_0RD---_1LD1RB_---1LD_------. -/
def p137 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none

theorem cert137 : zipCycle p137 11 1 false (-1) = true := by decide +kernel
theorem never137 (m : Machine) (hm : compatible p137 m) : NeverHalts m :=
  zipCycle_sound p137 11 1 false (-1) (by decide) cert137 m hm
#print axioms never137

/-- Raw45 first-hole depth 2, 1RB---_1RC1LE_0RD---_1LD1RB_---0RD_------. -/
def p138 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none

theorem cert138 : zipCycle p138 1 11 true (1) = true := by decide +kernel
theorem never138 (m : Machine) (hm : compatible p138 m) : NeverHalts m :=
  zipCycle_sound p138 1 11 true (1) (by decide) cert138 m hm
#print axioms never138

/-- Raw45 first-hole depth 2, 1RB---_1RC1LE_0RD---_1LD1RB_---1RD_------. -/
def p139 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none

theorem cert139 : zipCycle p139 1 11 true (1) = true := by decide +kernel
theorem never139 (m : Machine) (hm : compatible p139 m) : NeverHalts m :=
  zipCycle_sound p139 1 11 true (1) (by decide) cert139 m hm
#print axioms never139

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---0LA_------. -/
def p140 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none

theorem cert140 : zipCycle p140 0 8 true (0) = true := by decide +kernel
theorem never140 (m : Machine) (hm : compatible p140 m) : NeverHalts m :=
  zipCycle_sound p140 0 8 true (0) (by decide) cert140 m hm
#print axioms never140

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---0RA_------. -/
def p141 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none

theorem cert141 : zipCycle p141 0 8 true (0) = true := by decide +kernel
theorem never141 (m : Machine) (hm : compatible p141 m) : NeverHalts m :=
  zipCycle_sound p141 0 8 true (0) (by decide) cert141 m hm
#print axioms never141

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---1RA_------. -/
def p142 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem cert142 : zipCycle p142 0 8 true (0) = true := by decide +kernel
theorem never142 (m : Machine) (hm : compatible p142 m) : NeverHalts m :=
  zipCycle_sound p142 0 8 true (0) (by decide) cert142 m hm
#print axioms never142

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---0LB_------. -/
def p143 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none

theorem cert143 : zipCycle p143 1 7 true (1) = true := by decide +kernel
theorem never143 (m : Machine) (hm : compatible p143 m) : NeverHalts m :=
  zipCycle_sound p143 1 7 true (1) (by decide) cert143 m hm
#print axioms never143

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---0RB_------. -/
def p144 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none

theorem cert144 : zipCycle p144 1 7 true (1) = true := by decide +kernel
theorem never144 (m : Machine) (hm : compatible p144 m) : NeverHalts m :=
  zipCycle_sound p144 1 7 true (1) (by decide) cert144 m hm
#print axioms never144

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---1RB_------. -/
def p145 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert145 : zipCycle p145 1 7 true (1) = true := by decide +kernel
theorem never145 (m : Machine) (hm : compatible p145 m) : NeverHalts m :=
  zipCycle_sound p145 1 7 true (1) (by decide) cert145 m hm
#print axioms never145

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---0LC_------. -/
def p146 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none

theorem cert146 : zipCycle p146 2 6 true (1) = true := by decide +kernel
theorem never146 (m : Machine) (hm : compatible p146 m) : NeverHalts m :=
  zipCycle_sound p146 2 6 true (1) (by decide) cert146 m hm
#print axioms never146

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---1LC_------. -/
def p147 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none

theorem cert147 : zipCycle p147 1 9 true (1) = true := by decide +kernel
theorem never147 (m : Machine) (hm : compatible p147 m) : NeverHalts m :=
  zipCycle_sound p147 1 9 true (1) (by decide) cert147 m hm
#print axioms never147

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---1RC_------. -/
def p148 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none

theorem cert148 : zipCycle p148 2 6 true (1) = true := by decide +kernel
theorem never148 (m : Machine) (hm : compatible p148 m) : NeverHalts m :=
  zipCycle_sound p148 2 6 true (1) (by decide) cert148 m hm
#print axioms never148

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---1LD_------. -/
def p149 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none

theorem cert149 : zipCycle p149 4 4 true (1) = true := by decide +kernel
theorem never149 (m : Machine) (hm : compatible p149 m) : NeverHalts m :=
  zipCycle_sound p149 4 4 true (1) (by decide) cert149 m hm
#print axioms never149

/-- Raw45 first-hole depth 2, 1RB---_1RC0RE_0RD---_1LD1RB_---0RD_------. -/
def p150 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none

theorem cert150 : zipCycle p150 1 14 true (1) = true := by decide +kernel
theorem never150 (m : Machine) (hm : compatible p150 m) : NeverHalts m :=
  zipCycle_sound p150 1 14 true (1) (by decide) cert150 m hm
#print axioms never150

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---0RA_------. -/
def p151 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none

theorem cert151 : zipCycle p151 0 8 true (0) = true := by decide +kernel
theorem never151 (m : Machine) (hm : compatible p151 m) : NeverHalts m :=
  zipCycle_sound p151 0 8 true (0) (by decide) cert151 m hm
#print axioms never151

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---1RA_------. -/
def p152 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none

theorem cert152 : zipCycle p152 0 8 true (0) = true := by decide +kernel
theorem never152 (m : Machine) (hm : compatible p152 m) : NeverHalts m :=
  zipCycle_sound p152 0 8 true (0) (by decide) cert152 m hm
#print axioms never152

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---1LB_------. -/
def p153 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cert153 : zipCycle p153 6 2 true (2) = true := by decide +kernel
theorem never153 (m : Machine) (hm : compatible p153 m) : NeverHalts m :=
  zipCycle_sound p153 6 2 true (2) (by decide) cert153 m hm
#print axioms never153

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---0RB_------. -/
def p154 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none

theorem cert154 : zipCycle p154 1 7 true (1) = true := by decide +kernel
theorem never154 (m : Machine) (hm : compatible p154 m) : NeverHalts m :=
  zipCycle_sound p154 1 7 true (1) (by decide) cert154 m hm
#print axioms never154

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---1RB_------. -/
def p155 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert155 : zipCycle p155 1 7 true (1) = true := by decide +kernel
theorem never155 (m : Machine) (hm : compatible p155 m) : NeverHalts m :=
  zipCycle_sound p155 1 7 true (1) (by decide) cert155 m hm
#print axioms never155

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---1RC_------. -/
def p156 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none

theorem cert156 : zipCycle p156 2 6 true (1) = true := by decide +kernel
theorem never156 (m : Machine) (hm : compatible p156 m) : NeverHalts m :=
  zipCycle_sound p156 2 6 true (1) (by decide) cert156 m hm
#print axioms never156

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---0LD_------. -/
def p157 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none

theorem cert157 : zipCycle p157 1 8 true (1) = true := by decide +kernel
theorem never157 (m : Machine) (hm : compatible p157 m) : NeverHalts m :=
  zipCycle_sound p157 1 8 true (1) (by decide) cert157 m hm
#print axioms never157

/-- Raw45 first-hole depth 2, 1RB---_1RC1RE_0RD---_1LD1RB_---0RD_------. -/
def p158 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none

theorem cert158 : zipCycle p158 3 5 true (1) = true := by decide +kernel
theorem never158 (m : Machine) (hm : compatible p158 m) : NeverHalts m :=
  zipCycle_sound p158 3 5 true (1) (by decide) cert158 m hm
#print axioms never158
end BB6.Agent24Raw45D2D
