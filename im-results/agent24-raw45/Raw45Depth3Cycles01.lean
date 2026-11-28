import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_01
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 100, 1RB0RE_1RC0LA_0RD---_1LD1RB_1LD---_------; entry 14, period 1. -/
def p100 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert100 : zipCycle p100 14 1 false (0) = true := by decide +kernel
theorem never100 (m : Machine) (hm : compatible p100 m) : NeverHalts m :=
  zipCycle_sound p100 14 1 false (0) (by decide) cert100 m hm
#print axioms never100


/-- Third-level first-hole refinement 101, 1RB0RE_1RC0LA_0RD---_1LD1RB_0RD---_------; entry 1, period 9. -/
def p101 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert101 : zipCycle p101 1 9 true (1) = true := by decide +kernel
theorem never101 (m : Machine) (hm : compatible p101 m) : NeverHalts m :=
  zipCycle_sound p101 1 9 true (1) (by decide) cert101 m hm
#print axioms never101


/-- Third-level first-hole refinement 102, 1RB0RE_1RC0LA_0RD---_1LD1RB_1RD---_------; entry 1, period 9. -/
def p102 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert102 : zipCycle p102 1 9 true (1) = true := by decide +kernel
theorem never102 (m : Machine) (hm : compatible p102 m) : NeverHalts m :=
  zipCycle_sound p102 1 9 true (1) (by decide) cert102 m hm
#print axioms never102


/-- Third-level first-hole refinement 103, 1RB1RE_1RC0LA_0RD---_1LD1RB_0LA---_------; entry 7, period 2. -/
def p103 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert103 : zipCycle p103 7 2 true (1) = true := by decide +kernel
theorem never103 (m : Machine) (hm : compatible p103 m) : NeverHalts m :=
  zipCycle_sound p103 7 2 true (1) (by decide) cert103 m hm
#print axioms never103


/-- Third-level first-hole refinement 104, 1RB1RE_1RC0LA_0RD---_1LD1RB_0RA---_------; entry 0, period 11. -/
def p104 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert104 : zipCycle p104 0 11 true (0) = true := by decide +kernel
theorem never104 (m : Machine) (hm : compatible p104 m) : NeverHalts m :=
  zipCycle_sound p104 0 11 true (0) (by decide) cert104 m hm
#print axioms never104


/-- Third-level first-hole refinement 105, 1RB1RE_1RC0LA_0RD---_1LD1RB_1RA---_------; entry 0, period 11. -/
def p105 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert105 : zipCycle p105 0 11 true (0) = true := by decide +kernel
theorem never105 (m : Machine) (hm : compatible p105 m) : NeverHalts m :=
  zipCycle_sound p105 0 11 true (0) (by decide) cert105 m hm
#print axioms never105


/-- Third-level first-hole refinement 106, 1RB1RE_1RC0LA_0RD---_1LD1RB_0LB---_------; entry 0, period 13. -/
def p106 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert106 : zipCycle p106 0 13 false (3) = true := by decide +kernel
theorem never106 (m : Machine) (hm : compatible p106 m) : NeverHalts m :=
  zipCycle_sound p106 0 13 false (3) (by decide) cert106 m hm
#print axioms never106


/-- Third-level first-hole refinement 107, 1RB1RE_1RC0LA_0RD---_1LD1RB_0RB---_------; entry 0, period 10. -/
def p107 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert107 : zipCycle p107 0 10 true (0) = true := by decide +kernel
theorem never107 (m : Machine) (hm : compatible p107 m) : NeverHalts m :=
  zipCycle_sound p107 0 10 true (0) (by decide) cert107 m hm
#print axioms never107


/-- Third-level first-hole refinement 108, 1RB1RE_1RC0LA_0RD---_1LD1RB_1RB---_------; entry 1, period 11. -/
def p108 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert108 : zipCycle p108 1 11 true (1) = true := by decide +kernel
theorem never108 (m : Machine) (hm : compatible p108 m) : NeverHalts m :=
  zipCycle_sound p108 1 11 true (1) (by decide) cert108 m hm
#print axioms never108


/-- Third-level first-hole refinement 109, 1RB1RE_1RC0LA_0RD---_1LD1RB_1LD---_------; entry 5, period 4. -/
def p109 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert109 : zipCycle p109 5 4 true (1) = true := by decide +kernel
theorem never109 (m : Machine) (hm : compatible p109 m) : NeverHalts m :=
  zipCycle_sound p109 5 4 true (1) (by decide) cert109 m hm
#print axioms never109


/-- Third-level first-hole refinement 110, 1RB1RE_1RC0LA_0RD---_1LD1RB_0RD---_------; entry 1, period 9. -/
def p110 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert110 : zipCycle p110 1 9 true (1) = true := by decide +kernel
theorem never110 (m : Machine) (hm : compatible p110 m) : NeverHalts m :=
  zipCycle_sound p110 1 9 true (1) (by decide) cert110 m hm
#print axioms never110


/-- Third-level first-hole refinement 111, 1RB1RE_1RC0LA_0RD---_1LD1RB_1RD---_------; entry 1, period 9. -/
def p111 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert111 : zipCycle p111 1 9 true (1) = true := by decide +kernel
theorem never111 (m : Machine) (hm : compatible p111 m) : NeverHalts m :=
  zipCycle_sound p111 1 9 true (1) (by decide) cert111 m hm
#print axioms never111


/-- Third-level first-hole refinement 112, 1RB0LA_1RC1LA_0RD0LA_1LD1RB_------_------; entry 0, period 22. -/
def p112 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert112 : zipCycle p112 0 22 false (3) = true := by decide +kernel
theorem never112 (m : Machine) (hm : compatible p112 m) : NeverHalts m :=
  zipCycle_sound p112 0 22 false (3) (by decide) cert112 m hm
#print axioms never112


/-- Third-level first-hole refinement 113, 1RB0LA_1RC1LA_0RD1LA_1LD1RB_------_------; entry 0, period 22. -/
def p113 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert113 : zipCycle p113 0 22 false (3) = true := by decide +kernel
theorem never113 (m : Machine) (hm : compatible p113 m) : NeverHalts m :=
  zipCycle_sound p113 0 22 false (3) (by decide) cert113 m hm
#print axioms never113


/-- Third-level first-hole refinement 114, 1RB0LA_1RC1LA_0RD0RA_1LD1RB_------_------; entry 0, period 18. -/
def p114 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert114 : zipCycle p114 0 18 true (-1) = true := by decide +kernel
theorem never114 (m : Machine) (hm : compatible p114 m) : NeverHalts m :=
  zipCycle_sound p114 0 18 true (-1) (by decide) cert114 m hm
#print axioms never114


/-- Third-level first-hole refinement 115, 1RB0LA_1RC1LA_0RD1RA_1LD1RB_------_------; entry 0, period 32. -/
def p115 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert115 : zipCycle p115 0 32 false (7) = true := by decide +kernel
theorem never115 (m : Machine) (hm : compatible p115 m) : NeverHalts m :=
  zipCycle_sound p115 0 32 false (7) (by decide) cert115 m hm
#print axioms never115


/-- Third-level first-hole refinement 116, 1RB0LA_1RC1LA_0RD0LB_1LD1RB_------_------; entry 0, period 22. -/
def p116 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert116 : zipCycle p116 0 22 false (3) = true := by decide +kernel
theorem never116 (m : Machine) (hm : compatible p116 m) : NeverHalts m :=
  zipCycle_sound p116 0 22 false (3) (by decide) cert116 m hm
#print axioms never116


/-- Third-level first-hole refinement 117, 1RB0LA_1RC1LA_0RD1LB_1LD1RB_------_------; entry 0, period 22. -/
def p117 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert117 : zipCycle p117 0 22 false (3) = true := by decide +kernel
theorem never117 (m : Machine) (hm : compatible p117 m) : NeverHalts m :=
  zipCycle_sound p117 0 22 false (3) (by decide) cert117 m hm
#print axioms never117


/-- Third-level first-hole refinement 118, 1RB0LA_1RC1LA_0RD1RB_1LD1RB_------_------; entry 0, period 30. -/
def p118 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert118 : zipCycle p118 0 30 false (6) = true := by decide +kernel
theorem never118 (m : Machine) (hm : compatible p118 m) : NeverHalts m :=
  zipCycle_sound p118 0 30 false (6) (by decide) cert118 m hm
#print axioms never118


/-- Third-level first-hole refinement 119, 1RB0LA_1RC1LA_0RD0LC_1LD1RB_------_------; entry 23, period 1. -/
def p119 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert119 : zipCycle p119 23 1 false (-1) = true := by decide +kernel
theorem never119 (m : Machine) (hm : compatible p119 m) : NeverHalts m :=
  zipCycle_sound p119 23 1 false (-1) (by decide) cert119 m hm
#print axioms never119


/-- Third-level first-hole refinement 120, 1RB0LA_1RC1LA_0RD1LC_1LD1RB_------_------; entry 19, period 9. -/
def p120 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert120 : zipCycle p120 19 9 false (1) = true := by decide +kernel
theorem never120 (m : Machine) (hm : compatible p120 m) : NeverHalts m :=
  zipCycle_sound p120 19 9 false (1) (by decide) cert120 m hm
#print axioms never120


/-- Third-level first-hole refinement 121, 1RB0LA_1RC1LA_0RD1RC_1LD1RB_------_------; entry 0, period 28. -/
def p121 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert121 : zipCycle p121 0 28 false (5) = true := by decide +kernel
theorem never121 (m : Machine) (hm : compatible p121 m) : NeverHalts m :=
  zipCycle_sound p121 0 28 false (5) (by decide) cert121 m hm
#print axioms never121


/-- Third-level first-hole refinement 122, 1RB0LA_1RC1LA_0RD0LD_1LD1RB_------_------; entry 0, period 30. -/
def p122 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert122 : zipCycle p122 0 30 false (5) = true := by decide +kernel
theorem never122 (m : Machine) (hm : compatible p122 m) : NeverHalts m :=
  zipCycle_sound p122 0 30 false (5) (by decide) cert122 m hm
#print axioms never122


/-- Third-level first-hole refinement 123, 1RB0LA_1RC1LA_0RD1LD_1LD1RB_------_------; entry 0, period 24. -/
def p123 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert123 : zipCycle p123 0 24 false (3) = true := by decide +kernel
theorem never123 (m : Machine) (hm : compatible p123 m) : NeverHalts m :=
  zipCycle_sound p123 0 24 false (3) (by decide) cert123 m hm
#print axioms never123


/-- Third-level first-hole refinement 124, 1RB0LA_1RC1LA_0RD0RD_1LD1RB_------_------; entry 0, period 26. -/
def p124 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert124 : zipCycle p124 0 26 false (4) = true := by decide +kernel
theorem never124 (m : Machine) (hm : compatible p124 m) : NeverHalts m :=
  zipCycle_sound p124 0 26 false (4) (by decide) cert124 m hm
#print axioms never124


/-- Third-level first-hole refinement 125, 1RB0LA_1RC1LA_0RD1RD_1LD1RB_------_------; entry 0, period 26. -/
def p125 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert125 : zipCycle p125 0 26 false (4) = true := by decide +kernel
theorem never125 (m : Machine) (hm : compatible p125 m) : NeverHalts m :=
  zipCycle_sound p125 0 26 false (4) (by decide) cert125 m hm
#print axioms never125


/-- Third-level first-hole refinement 126, 1RB0LB_1RC1LA_0RD0LA_1LD1RB_------_------; entry 6, period 14. -/
def p126 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert126 : zipCycle p126 6 14 false (2) = true := by decide +kernel
theorem never126 (m : Machine) (hm : compatible p126 m) : NeverHalts m :=
  zipCycle_sound p126 6 14 false (2) (by decide) cert126 m hm
#print axioms never126


/-- Third-level first-hole refinement 127, 1RB0LB_1RC1LA_0RD1LA_1LD1RB_------_------; entry 6, period 14. -/
def p127 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert127 : zipCycle p127 6 14 false (2) = true := by decide +kernel
theorem never127 (m : Machine) (hm : compatible p127 m) : NeverHalts m :=
  zipCycle_sound p127 6 14 false (2) (by decide) cert127 m hm
#print axioms never127


/-- Third-level first-hole refinement 128, 1RB0LB_1RC1LA_0RD0RA_1LD1RB_------_------; entry 10, period 15. -/
def p128 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert128 : zipCycle p128 10 15 true (-2) = true := by decide +kernel
theorem never128 (m : Machine) (hm : compatible p128 m) : NeverHalts m :=
  zipCycle_sound p128 10 15 true (-2) (by decide) cert128 m hm
#print axioms never128


/-- Third-level first-hole refinement 129, 1RB0LB_1RC1LA_0RD1RA_1LD1RB_------_------; entry 17, period 18. -/
def p129 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert129 : zipCycle p129 17 18 false (3) = true := by decide +kernel
theorem never129 (m : Machine) (hm : compatible p129 m) : NeverHalts m :=
  zipCycle_sound p129 17 18 false (3) (by decide) cert129 m hm
#print axioms never129


/-- Third-level first-hole refinement 130, 1RB0LB_1RC1LA_0RD1LD_1LD1RB_------_------; entry 6, period 16. -/
def p130 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert130 : zipCycle p130 6 16 false (2) = true := by decide +kernel
theorem never130 (m : Machine) (hm : compatible p130 m) : NeverHalts m :=
  zipCycle_sound p130 6 16 false (2) (by decide) cert130 m hm
#print axioms never130


/-- Third-level first-hole refinement 131, 1RB0LB_1RC1LA_0RD0RD_1LD1RB_------_------; entry 45, period 18. -/
def p131 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert131 : zipCycle p131 45 18 false (2) = true := by decide +kernel
theorem never131 (m : Machine) (hm : compatible p131 m) : NeverHalts m :=
  zipCycle_sound p131 45 18 false (2) (by decide) cert131 m hm
#print axioms never131


/-- Third-level first-hole refinement 132, 1RB1LB_1RC1LA_0RD0LA_1LD1RB_------_------; entry 11, period 3. -/
def p132 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert132 : zipCycle p132 11 3 false (-1) = true := by decide +kernel
theorem never132 (m : Machine) (hm : compatible p132 m) : NeverHalts m :=
  zipCycle_sound p132 11 3 false (-1) (by decide) cert132 m hm
#print axioms never132


/-- Third-level first-hole refinement 133, 1RB1LB_1RC1LA_0RD1LA_1LD1RB_------_------; entry 11, period 3. -/
def p133 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert133 : zipCycle p133 11 3 false (-1) = true := by decide +kernel
theorem never133 (m : Machine) (hm : compatible p133 m) : NeverHalts m :=
  zipCycle_sound p133 11 3 false (-1) (by decide) cert133 m hm
#print axioms never133


/-- Third-level first-hole refinement 134, 1RB1LB_1RC1LA_0RD1RA_1LD1RB_------_------; entry 10, period 5. -/
def p134 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert134 : zipCycle p134 10 5 false (0) = true := by decide +kernel
theorem never134 (m : Machine) (hm : compatible p134 m) : NeverHalts m :=
  zipCycle_sound p134 10 5 false (0) (by decide) cert134 m hm
#print axioms never134


/-- Third-level first-hole refinement 135, 1RB1LB_1RC1LA_0RD0LB_1LD1RB_------_------; entry 8, period 6. -/
def p135 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert135 : zipCycle p135 8 6 false (0) = true := by decide +kernel
theorem never135 (m : Machine) (hm : compatible p135 m) : NeverHalts m :=
  zipCycle_sound p135 8 6 false (0) (by decide) cert135 m hm
#print axioms never135


/-- Third-level first-hole refinement 136, 1RB1LB_1RC1LA_0RD1LB_1LD1RB_------_------; entry 8, period 6. -/
def p136 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert136 : zipCycle p136 8 6 false (0) = true := by decide +kernel
theorem never136 (m : Machine) (hm : compatible p136 m) : NeverHalts m :=
  zipCycle_sound p136 8 6 false (0) (by decide) cert136 m hm
#print axioms never136


/-- Third-level first-hole refinement 137, 1RB1LB_1RC1LA_0RD0RB_1LD1RB_------_------; entry 6, period 10. -/
def p137 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert137 : zipCycle p137 6 10 false (2) = true := by decide +kernel
theorem never137 (m : Machine) (hm : compatible p137 m) : NeverHalts m :=
  zipCycle_sound p137 6 10 false (2) (by decide) cert137 m hm
#print axioms never137


/-- Third-level first-hole refinement 138, 1RB1LB_1RC1LA_0RD1RB_1LD1RB_------_------; entry 6, period 8. -/
def p138 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert138 : zipCycle p138 6 8 false (2) = true := by decide +kernel
theorem never138 (m : Machine) (hm : compatible p138 m) : NeverHalts m :=
  zipCycle_sound p138 6 8 false (2) (by decide) cert138 m hm
#print axioms never138


/-- Third-level first-hole refinement 139, 1RB1LB_1RC1LA_0RD0LC_1LD1RB_------_------; entry 16, period 1. -/
def p139 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert139 : zipCycle p139 16 1 false (-2) = true := by decide +kernel
theorem never139 (m : Machine) (hm : compatible p139 m) : NeverHalts m :=
  zipCycle_sound p139 16 1 false (-2) (by decide) cert139 m hm
#print axioms never139


/-- Third-level first-hole refinement 140, 1RB1LB_1RC1LA_0RD1LC_1LD1RB_------_------; entry 10, period 7. -/
def p140 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert140 : zipCycle p140 10 7 false (0) = true := by decide +kernel
theorem never140 (m : Machine) (hm : compatible p140 m) : NeverHalts m :=
  zipCycle_sound p140 10 7 false (0) (by decide) cert140 m hm
#print axioms never140


/-- Third-level first-hole refinement 141, 1RB1LB_1RC1LA_0RD1LD_1LD1RB_------_------; entry 10, period 5. -/
def p141 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert141 : zipCycle p141 10 5 false (0) = true := by decide +kernel
theorem never141 (m : Machine) (hm : compatible p141 m) : NeverHalts m :=
  zipCycle_sound p141 10 5 false (0) (by decide) cert141 m hm
#print axioms never141


/-- Third-level first-hole refinement 142, 1RB1LB_1RC1LA_0RD1RD_1LD1RB_------_------; entry 10, period 7. -/
def p142 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert142 : zipCycle p142 10 7 false (1) = true := by decide +kernel
theorem never142 (m : Machine) (hm : compatible p142 m) : NeverHalts m :=
  zipCycle_sound p142 10 7 false (1) (by decide) cert142 m hm
#print axioms never142


/-- Third-level first-hole refinement 143, 1RB0LC_1RC1LA_0RD0LA_1LD1RB_------_------; entry 2, period 13. -/
def p143 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert143 : zipCycle p143 2 13 false (3) = true := by decide +kernel
theorem never143 (m : Machine) (hm : compatible p143 m) : NeverHalts m :=
  zipCycle_sound p143 2 13 false (3) (by decide) cert143 m hm
#print axioms never143


/-- Third-level first-hole refinement 144, 1RB0LC_1RC1LA_0RD1LA_1LD1RB_------_------; entry 13, period 1. -/
def p144 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert144 : zipCycle p144 13 1 false (-1) = true := by decide +kernel
theorem never144 (m : Machine) (hm : compatible p144 m) : NeverHalts m :=
  zipCycle_sound p144 13 1 false (-1) (by decide) cert144 m hm
#print axioms never144


/-- Third-level first-hole refinement 145, 1RB0LC_1RC1LA_0RD0RA_1LD1RB_------_------; entry 13, period 1. -/
def p145 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert145 : zipCycle p145 13 1 false (1) = true := by decide +kernel
theorem never145 (m : Machine) (hm : compatible p145 m) : NeverHalts m :=
  zipCycle_sound p145 13 1 false (1) (by decide) cert145 m hm
#print axioms never145


/-- Third-level first-hole refinement 146, 1RB0LC_1RC1LA_0RD1RA_1LD1RB_------_------; entry 6, period 4. -/
def p146 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert146 : zipCycle p146 6 4 true (0) = true := by decide +kernel
theorem never146 (m : Machine) (hm : compatible p146 m) : NeverHalts m :=
  zipCycle_sound p146 6 4 true (0) (by decide) cert146 m hm
#print axioms never146


/-- Third-level first-hole refinement 147, 1RB0LC_1RC1LA_0RD0LB_1LD1RB_------_------; entry 17, period 1. -/
def p147 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert147 : zipCycle p147 17 1 false (-1) = true := by decide +kernel
theorem never147 (m : Machine) (hm : compatible p147 m) : NeverHalts m :=
  zipCycle_sound p147 17 1 false (-1) (by decide) cert147 m hm
#print axioms never147


/-- Third-level first-hole refinement 148, 1RB0LC_1RC1LA_0RD1LB_1LD1RB_------_------; entry 16, period 1. -/
def p148 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert148 : zipCycle p148 16 1 false (-2) = true := by decide +kernel
theorem never148 (m : Machine) (hm : compatible p148 m) : NeverHalts m :=
  zipCycle_sound p148 16 1 false (-2) (by decide) cert148 m hm
#print axioms never148


/-- Third-level first-hole refinement 149, 1RB0LC_1RC1LA_0RD0RB_1LD1RB_------_------; entry 32, period 1. -/
def p149 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert149 : zipCycle p149 32 1 false (2) = true := by decide +kernel
theorem never149 (m : Machine) (hm : compatible p149 m) : NeverHalts m :=
  zipCycle_sound p149 32 1 false (2) (by decide) cert149 m hm
#print axioms never149


/-- Third-level first-hole refinement 150, 1RB0LC_1RC1LA_0RD1RB_1LD1RB_------_------; entry 1, period 15. -/
def p150 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert150 : zipCycle p150 1 15 true (0) = true := by decide +kernel
theorem never150 (m : Machine) (hm : compatible p150 m) : NeverHalts m :=
  zipCycle_sound p150 1 15 true (0) (by decide) cert150 m hm
#print axioms never150


/-- Third-level first-hole refinement 151, 1RB0LC_1RC1LA_0RD0LC_1LD1RB_------_------; entry 10, period 1. -/
def p151 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert151 : zipCycle p151 10 1 false (0) = true := by decide +kernel
theorem never151 (m : Machine) (hm : compatible p151 m) : NeverHalts m :=
  zipCycle_sound p151 10 1 false (0) (by decide) cert151 m hm
#print axioms never151


/-- Third-level first-hole refinement 152, 1RB0LC_1RC1LA_0RD1LC_1LD1RB_------_------; entry 20, period 1. -/
def p152 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert152 : zipCycle p152 20 1 false (0) = true := by decide +kernel
theorem never152 (m : Machine) (hm : compatible p152 m) : NeverHalts m :=
  zipCycle_sound p152 20 1 false (0) (by decide) cert152 m hm
#print axioms never152


/-- Third-level first-hole refinement 153, 1RB0LC_1RC1LA_0RD0RC_1LD1RB_------_------; entry 14, period 1. -/
def p153 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert153 : zipCycle p153 14 1 false (2) = true := by decide +kernel
theorem never153 (m : Machine) (hm : compatible p153 m) : NeverHalts m :=
  zipCycle_sound p153 14 1 false (2) (by decide) cert153 m hm
#print axioms never153


/-- Third-level first-hole refinement 154, 1RB0LC_1RC1LA_0RD1RC_1LD1RB_------_------; entry 20, period 1. -/
def p154 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert154 : zipCycle p154 20 1 false (0) = true := by decide +kernel
theorem never154 (m : Machine) (hm : compatible p154 m) : NeverHalts m :=
  zipCycle_sound p154 20 1 false (0) (by decide) cert154 m hm
#print axioms never154


/-- Third-level first-hole refinement 155, 1RB0LC_1RC1LA_0RD0LD_1LD1RB_------_------; entry 9, period 1. -/
def p155 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert155 : zipCycle p155 9 1 false (-1) = true := by decide +kernel
theorem never155 (m : Machine) (hm : compatible p155 m) : NeverHalts m :=
  zipCycle_sound p155 9 1 false (-1) (by decide) cert155 m hm
#print axioms never155


/-- Third-level first-hole refinement 156, 1RB0LC_1RC1LA_0RD1LD_1LD1RB_------_------; entry 9, period 1. -/
def p156 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert156 : zipCycle p156 9 1 false (-1) = true := by decide +kernel
theorem never156 (m : Machine) (hm : compatible p156 m) : NeverHalts m :=
  zipCycle_sound p156 9 1 false (-1) (by decide) cert156 m hm
#print axioms never156


/-- Third-level first-hole refinement 157, 1RB0LC_1RC1LA_0RD0RD_1LD1RB_------_------; entry 9, period 1. -/
def p157 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert157 : zipCycle p157 9 1 false (1) = true := by decide +kernel
theorem never157 (m : Machine) (hm : compatible p157 m) : NeverHalts m :=
  zipCycle_sound p157 9 1 false (1) (by decide) cert157 m hm
#print axioms never157


/-- Third-level first-hole refinement 158, 1RB0LC_1RC1LA_0RD1RD_1LD1RB_------_------; entry 14, period 1. -/
def p158 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert158 : zipCycle p158 14 1 false (0) = true := by decide +kernel
theorem never158 (m : Machine) (hm : compatible p158 m) : NeverHalts m :=
  zipCycle_sound p158 14 1 false (0) (by decide) cert158 m hm
#print axioms never158


/-- Third-level first-hole refinement 159, 1RB1LC_1RC1LA_0RD0LA_1LD1RB_------_------; entry 7, period 5. -/
def p159 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert159 : zipCycle p159 7 5 false (1) = true := by decide +kernel
theorem never159 (m : Machine) (hm : compatible p159 m) : NeverHalts m :=
  zipCycle_sound p159 7 5 false (1) (by decide) cert159 m hm
#print axioms never159


/-- Third-level first-hole refinement 160, 1RB1LC_1RC1LA_0RD1LA_1LD1RB_------_------; entry 10, period 4. -/
def p160 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert160 : zipCycle p160 10 4 true (-2) = true := by decide +kernel
theorem never160 (m : Machine) (hm : compatible p160 m) : NeverHalts m :=
  zipCycle_sound p160 10 4 true (-2) (by decide) cert160 m hm
#print axioms never160


/-- Third-level first-hole refinement 161, 1RB1LC_1RC1LA_0RD0RA_1LD1RB_------_------; entry 9, period 4. -/
def p161 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert161 : zipCycle p161 9 4 true (0) = true := by decide +kernel
theorem never161 (m : Machine) (hm : compatible p161 m) : NeverHalts m :=
  zipCycle_sound p161 9 4 true (0) (by decide) cert161 m hm
#print axioms never161


/-- Third-level first-hole refinement 162, 1RB1LC_1RC1LA_0RD1RA_1LD1RB_------_------; entry 7, period 2. -/
def p162 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert162 : zipCycle p162 7 2 true (0) = true := by decide +kernel
theorem never162 (m : Machine) (hm : compatible p162 m) : NeverHalts m :=
  zipCycle_sound p162 7 2 true (0) (by decide) cert162 m hm
#print axioms never162


/-- Third-level first-hole refinement 163, 1RB1LC_1RC1LA_0RD0LB_1LD1RB_------_------; entry 10, period 4. -/
def p163 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert163 : zipCycle p163 10 4 true (0) = true := by decide +kernel
theorem never163 (m : Machine) (hm : compatible p163 m) : NeverHalts m :=
  zipCycle_sound p163 10 4 true (0) (by decide) cert163 m hm
#print axioms never163


/-- Third-level first-hole refinement 164, 1RB1LC_1RC1LA_0RD1LB_1LD1RB_------_------; entry 13, period 4. -/
def p164 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert164 : zipCycle p164 13 4 true (-3) = true := by decide +kernel
theorem never164 (m : Machine) (hm : compatible p164 m) : NeverHalts m :=
  zipCycle_sound p164 13 4 true (-3) (by decide) cert164 m hm
#print axioms never164


/-- Third-level first-hole refinement 165, 1RB1LC_1RC1LA_0RD0RB_1LD1RB_------_------; entry 11, period 4. -/
def p165 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert165 : zipCycle p165 11 4 true (-1) = true := by decide +kernel
theorem never165 (m : Machine) (hm : compatible p165 m) : NeverHalts m :=
  zipCycle_sound p165 11 4 true (-1) (by decide) cert165 m hm
#print axioms never165


/-- Third-level first-hole refinement 166, 1RB1LC_1RC1LA_0RD1RB_1LD1RB_------_------; entry 9, period 4. -/
def p166 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert166 : zipCycle p166 9 4 true (-1) = true := by decide +kernel
theorem never166 (m : Machine) (hm : compatible p166 m) : NeverHalts m :=
  zipCycle_sound p166 9 4 true (-1) (by decide) cert166 m hm
#print axioms never166


/-- Third-level first-hole refinement 167, 1RB1LC_1RC1LA_0RD0LC_1LD1RB_------_------; entry 10, period 1. -/
def p167 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert167 : zipCycle p167 10 1 false (0) = true := by decide +kernel
theorem never167 (m : Machine) (hm : compatible p167 m) : NeverHalts m :=
  zipCycle_sound p167 10 1 false (0) (by decide) cert167 m hm
#print axioms never167


/-- Third-level first-hole refinement 168, 1RB1LC_1RC1LA_0RD1LC_1LD1RB_------_------; entry 9, period 4. -/
def p168 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert168 : zipCycle p168 9 4 true (-1) = true := by decide +kernel
theorem never168 (m : Machine) (hm : compatible p168 m) : NeverHalts m :=
  zipCycle_sound p168 9 4 true (-1) (by decide) cert168 m hm
#print axioms never168


/-- Third-level first-hole refinement 169, 1RB1LC_1RC1LA_0RD0RC_1LD1RB_------_------; entry 13, period 1. -/
def p169 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert169 : zipCycle p169 13 1 false (5) = true := by decide +kernel
theorem never169 (m : Machine) (hm : compatible p169 m) : NeverHalts m :=
  zipCycle_sound p169 13 1 false (5) (by decide) cert169 m hm
#print axioms never169


/-- Third-level first-hole refinement 170, 1RB1LC_1RC1LA_0RD1RC_1LD1RB_------_------; entry 2, period 10. -/
def p170 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert170 : zipCycle p170 2 10 true (0) = true := by decide +kernel
theorem never170 (m : Machine) (hm : compatible p170 m) : NeverHalts m :=
  zipCycle_sound p170 2 10 true (0) (by decide) cert170 m hm
#print axioms never170


/-- Third-level first-hole refinement 171, 1RB1LC_1RC1LA_0RD0LD_1LD1RB_------_------; entry 9, period 1. -/
def p171 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert171 : zipCycle p171 9 1 false (-1) = true := by decide +kernel
theorem never171 (m : Machine) (hm : compatible p171 m) : NeverHalts m :=
  zipCycle_sound p171 9 1 false (-1) (by decide) cert171 m hm
#print axioms never171


/-- Third-level first-hole refinement 172, 1RB1LC_1RC1LA_0RD1LD_1LD1RB_------_------; entry 9, period 1. -/
def p172 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert172 : zipCycle p172 9 1 false (-1) = true := by decide +kernel
theorem never172 (m : Machine) (hm : compatible p172 m) : NeverHalts m :=
  zipCycle_sound p172 9 1 false (-1) (by decide) cert172 m hm
#print axioms never172


/-- Third-level first-hole refinement 173, 1RB1LC_1RC1LA_0RD0RD_1LD1RB_------_------; entry 9, period 4. -/
def p173 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert173 : zipCycle p173 9 4 true (0) = true := by decide +kernel
theorem never173 (m : Machine) (hm : compatible p173 m) : NeverHalts m :=
  zipCycle_sound p173 9 4 true (0) (by decide) cert173 m hm
#print axioms never173


/-- Third-level first-hole refinement 174, 1RB1LC_1RC1LA_0RD1RD_1LD1RB_------_------; entry 5, period 4. -/
def p174 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert174 : zipCycle p174 5 4 true (0) = true := by decide +kernel
theorem never174 (m : Machine) (hm : compatible p174 m) : NeverHalts m :=
  zipCycle_sound p174 5 4 true (0) (by decide) cert174 m hm
#print axioms never174


/-- Third-level first-hole refinement 175, 1RB0RC_1RC1LA_0RD0LA_1LD1RB_------_------; entry 1, period 26. -/
def p175 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert175 : zipCycle p175 1 26 true (1) = true := by decide +kernel
theorem never175 (m : Machine) (hm : compatible p175 m) : NeverHalts m :=
  zipCycle_sound p175 1 26 true (1) (by decide) cert175 m hm
#print axioms never175


/-- Third-level first-hole refinement 176, 1RB0RC_1RC1LA_0RD1LA_1LD1RB_------_------; entry 6, period 4. -/
def p176 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert176 : zipCycle p176 6 4 true (1) = true := by decide +kernel
theorem never176 (m : Machine) (hm : compatible p176 m) : NeverHalts m :=
  zipCycle_sound p176 6 4 true (1) (by decide) cert176 m hm
#print axioms never176


/-- Third-level first-hole refinement 177, 1RB0RC_1RC1LA_0RD0RA_1LD1RB_------_------; entry 0, period 24. -/
def p177 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert177 : zipCycle p177 0 24 true (0) = true := by decide +kernel
theorem never177 (m : Machine) (hm : compatible p177 m) : NeverHalts m :=
  zipCycle_sound p177 0 24 true (0) (by decide) cert177 m hm
#print axioms never177


/-- Third-level first-hole refinement 178, 1RB0RC_1RC1LA_0RD1RA_1LD1RB_------_------; entry 0, period 20. -/
def p178 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert178 : zipCycle p178 0 20 true (0) = true := by decide +kernel
theorem never178 (m : Machine) (hm : compatible p178 m) : NeverHalts m :=
  zipCycle_sound p178 0 20 true (0) (by decide) cert178 m hm
#print axioms never178


/-- Third-level first-hole refinement 179, 1RB0RC_1RC1LA_0RD0LB_1LD1RB_------_------; entry 1, period 11. -/
def p179 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert179 : zipCycle p179 1 11 true (1) = true := by decide +kernel
theorem never179 (m : Machine) (hm : compatible p179 m) : NeverHalts m :=
  zipCycle_sound p179 1 11 true (1) (by decide) cert179 m hm
#print axioms never179


/-- Third-level first-hole refinement 180, 1RB0RC_1RC1LA_0RD1LB_1LD1RB_------_------; entry 11, period 7. -/
def p180 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert180 : zipCycle p180 11 7 false (1) = true := by decide +kernel
theorem never180 (m : Machine) (hm : compatible p180 m) : NeverHalts m :=
  zipCycle_sound p180 11 7 false (1) (by decide) cert180 m hm
#print axioms never180


/-- Third-level first-hole refinement 181, 1RB0RC_1RC1LA_0RD0RB_1LD1RB_------_------; entry 1, period 13. -/
def p181 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert181 : zipCycle p181 1 13 true (1) = true := by decide +kernel
theorem never181 (m : Machine) (hm : compatible p181 m) : NeverHalts m :=
  zipCycle_sound p181 1 13 true (1) (by decide) cert181 m hm
#print axioms never181


/-- Third-level first-hole refinement 182, 1RB0RC_1RC1LA_0RD1RB_1LD1RB_------_------; entry 1, period 11. -/
def p182 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert182 : zipCycle p182 1 11 true (1) = true := by decide +kernel
theorem never182 (m : Machine) (hm : compatible p182 m) : NeverHalts m :=
  zipCycle_sound p182 1 11 true (1) (by decide) cert182 m hm
#print axioms never182


/-- Third-level first-hole refinement 183, 1RB0RC_1RC1LA_0RD0LC_1LD1RB_------_------; entry 17, period 1. -/
def p183 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert183 : zipCycle p183 17 1 false (1) = true := by decide +kernel
theorem never183 (m : Machine) (hm : compatible p183 m) : NeverHalts m :=
  zipCycle_sound p183 17 1 false (1) (by decide) cert183 m hm
#print axioms never183


/-- Third-level first-hole refinement 184, 1RB0RC_1RC1LA_0RD1LC_1LD1RB_------_------; entry 1, period 15. -/
def p184 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert184 : zipCycle p184 1 15 true (1) = true := by decide +kernel
theorem never184 (m : Machine) (hm : compatible p184 m) : NeverHalts m :=
  zipCycle_sound p184 1 15 true (1) (by decide) cert184 m hm
#print axioms never184


/-- Third-level first-hole refinement 185, 1RB0RC_1RC1LA_0RD0RC_1LD1RB_------_------; entry 25, period 1. -/
def p185 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert185 : zipCycle p185 25 1 false (7) = true := by decide +kernel
theorem never185 (m : Machine) (hm : compatible p185 m) : NeverHalts m :=
  zipCycle_sound p185 25 1 false (7) (by decide) cert185 m hm
#print axioms never185


/-- Third-level first-hole refinement 186, 1RB0RC_1RC1LA_0RD1RC_1LD1RB_------_------; entry 2, period 8. -/
def p186 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert186 : zipCycle p186 2 8 true (1) = true := by decide +kernel
theorem never186 (m : Machine) (hm : compatible p186 m) : NeverHalts m :=
  zipCycle_sound p186 2 8 true (1) (by decide) cert186 m hm
#print axioms never186


/-- Third-level first-hole refinement 187, 1RB0RC_1RC1LA_0RD0LD_1LD1RB_------_------; entry 14, period 1. -/
def p187 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert187 : zipCycle p187 14 1 false (0) = true := by decide +kernel
theorem never187 (m : Machine) (hm : compatible p187 m) : NeverHalts m :=
  zipCycle_sound p187 14 1 false (0) (by decide) cert187 m hm
#print axioms never187


/-- Third-level first-hole refinement 188, 1RB0RC_1RC1LA_0RD1LD_1LD1RB_------_------; entry 14, period 1. -/
def p188 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert188 : zipCycle p188 14 1 false (0) = true := by decide +kernel
theorem never188 (m : Machine) (hm : compatible p188 m) : NeverHalts m :=
  zipCycle_sound p188 14 1 false (0) (by decide) cert188 m hm
#print axioms never188


/-- Third-level first-hole refinement 189, 1RB0RC_1RC1LA_0RD0RD_1LD1RB_------_------; entry 1, period 9. -/
def p189 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert189 : zipCycle p189 1 9 true (1) = true := by decide +kernel
theorem never189 (m : Machine) (hm : compatible p189 m) : NeverHalts m :=
  zipCycle_sound p189 1 9 true (1) (by decide) cert189 m hm
#print axioms never189


/-- Third-level first-hole refinement 190, 1RB0RC_1RC1LA_0RD1RD_1LD1RB_------_------; entry 1, period 9. -/
def p190 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert190 : zipCycle p190 1 9 true (1) = true := by decide +kernel
theorem never190 (m : Machine) (hm : compatible p190 m) : NeverHalts m :=
  zipCycle_sound p190 1 9 true (1) (by decide) cert190 m hm
#print axioms never190


/-- Third-level first-hole refinement 191, 1RB1RC_1RC1LA_0RD0LA_1LD1RB_------_------; entry 1, period 11. -/
def p191 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert191 : zipCycle p191 1 11 true (1) = true := by decide +kernel
theorem never191 (m : Machine) (hm : compatible p191 m) : NeverHalts m :=
  zipCycle_sound p191 1 11 true (1) (by decide) cert191 m hm
#print axioms never191


/-- Third-level first-hole refinement 192, 1RB1RC_1RC1LA_0RD1LA_1LD1RB_------_------; entry 7, period 2. -/
def p192 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert192 : zipCycle p192 7 2 true (1) = true := by decide +kernel
theorem never192 (m : Machine) (hm : compatible p192 m) : NeverHalts m :=
  zipCycle_sound p192 7 2 true (1) (by decide) cert192 m hm
#print axioms never192


/-- Third-level first-hole refinement 193, 1RB1RC_1RC1LA_0RD0RA_1LD1RB_------_------; entry 2, period 8. -/
def p193 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert193 : zipCycle p193 2 8 true (1) = true := by decide +kernel
theorem never193 (m : Machine) (hm : compatible p193 m) : NeverHalts m :=
  zipCycle_sound p193 2 8 true (1) (by decide) cert193 m hm
#print axioms never193


/-- Third-level first-hole refinement 194, 1RB1RC_1RC1LA_0RD1RA_1LD1RB_------_------; entry 2, period 8. -/
def p194 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert194 : zipCycle p194 2 8 true (1) = true := by decide +kernel
theorem never194 (m : Machine) (hm : compatible p194 m) : NeverHalts m :=
  zipCycle_sound p194 2 8 true (1) (by decide) cert194 m hm
#print axioms never194


/-- Third-level first-hole refinement 195, 1RB1RC_1RC1LA_0RD0LB_1LD1RB_------_------; entry 9, period 5. -/
def p195 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert195 : zipCycle p195 9 5 false (1) = true := by decide +kernel
theorem never195 (m : Machine) (hm : compatible p195 m) : NeverHalts m :=
  zipCycle_sound p195 9 5 false (1) (by decide) cert195 m hm
#print axioms never195


/-- Third-level first-hole refinement 196, 1RB1RC_1RC1LA_0RD1LB_1LD1RB_------_------; entry 9, period 5. -/
def p196 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert196 : zipCycle p196 9 5 false (1) = true := by decide +kernel
theorem never196 (m : Machine) (hm : compatible p196 m) : NeverHalts m :=
  zipCycle_sound p196 9 5 false (1) (by decide) cert196 m hm
#print axioms never196


/-- Third-level first-hole refinement 197, 1RB1RC_1RC1LA_0RD0RB_1LD1RB_------_------; entry 1, period 13. -/
def p197 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert197 : zipCycle p197 1 13 true (1) = true := by decide +kernel
theorem never197 (m : Machine) (hm : compatible p197 m) : NeverHalts m :=
  zipCycle_sound p197 1 13 true (1) (by decide) cert197 m hm
#print axioms never197


/-- Third-level first-hole refinement 198, 1RB1RC_1RC1LA_0RD1RB_1LD1RB_------_------; entry 1, period 11. -/
def p198 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert198 : zipCycle p198 1 11 true (1) = true := by decide +kernel
theorem never198 (m : Machine) (hm : compatible p198 m) : NeverHalts m :=
  zipCycle_sound p198 1 11 true (1) (by decide) cert198 m hm
#print axioms never198


/-- Third-level first-hole refinement 199, 1RB1RC_1RC1LA_0RD0LC_1LD1RB_------_------; entry 12, period 1. -/
def p199 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,false,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert199 : zipCycle p199 12 1 false (0) = true := by decide +kernel
theorem never199 (m : Machine) (hm : compatible p199 m) : NeverHalts m :=
  zipCycle_sound p199 12 1 false (0) (by decide) cert199 m hm
#print axioms never199

end BB6.Agent24Raw45D3_01
