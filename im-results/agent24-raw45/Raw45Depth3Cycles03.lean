import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_03
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 300, 1RB0RE_1RC0RA_0RD---_1LD1RB_1RA---_------; entry 0, period 9. -/
def p300 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert300 : zipCycle p300 0 9 true (0) = true := by decide +kernel
theorem never300 (m : Machine) (hm : compatible p300 m) : NeverHalts m :=
  zipCycle_sound p300 0 9 true (0) (by decide) cert300 m hm
#print axioms never300


/-- Third-level first-hole refinement 301, 1RB0RE_1RC0RA_0RD---_1LD1RB_0LB---_------; entry 1, period 8. -/
def p301 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert301 : zipCycle p301 1 8 true (1) = true := by decide +kernel
theorem never301 (m : Machine) (hm : compatible p301 m) : NeverHalts m :=
  zipCycle_sound p301 1 8 true (1) (by decide) cert301 m hm
#print axioms never301


/-- Third-level first-hole refinement 302, 1RB0RE_1RC0RA_0RD---_1LD1RB_0RB---_------; entry 1, period 8. -/
def p302 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert302 : zipCycle p302 1 8 true (1) = true := by decide +kernel
theorem never302 (m : Machine) (hm : compatible p302 m) : NeverHalts m :=
  zipCycle_sound p302 1 8 true (1) (by decide) cert302 m hm
#print axioms never302


/-- Third-level first-hole refinement 303, 1RB0RE_1RC0RA_0RD---_1LD1RB_1RB---_------; entry 1, period 8. -/
def p303 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert303 : zipCycle p303 1 8 true (1) = true := by decide +kernel
theorem never303 (m : Machine) (hm : compatible p303 m) : NeverHalts m :=
  zipCycle_sound p303 1 8 true (1) (by decide) cert303 m hm
#print axioms never303


/-- Third-level first-hole refinement 304, 1RB0RE_1RC0RA_0RD---_1LD1RB_1LC---_------; entry 1, period 10. -/
def p304 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert304 : zipCycle p304 1 10 true (1) = true := by decide +kernel
theorem never304 (m : Machine) (hm : compatible p304 m) : NeverHalts m :=
  zipCycle_sound p304 1 10 true (1) (by decide) cert304 m hm
#print axioms never304


/-- Third-level first-hole refinement 305, 1RB0RE_1RC0RA_0RD---_1LD1RB_1RC---_------; entry 2, period 7. -/
def p305 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert305 : zipCycle p305 2 7 true (1) = true := by decide +kernel
theorem never305 (m : Machine) (hm : compatible p305 m) : NeverHalts m :=
  zipCycle_sound p305 2 7 true (1) (by decide) cert305 m hm
#print axioms never305


/-- Third-level first-hole refinement 306, 1RB0RE_1RC0RA_0RD---_1LD1RB_0LD---_------; entry 3, period 6. -/
def p306 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert306 : zipCycle p306 3 6 true (1) = true := by decide +kernel
theorem never306 (m : Machine) (hm : compatible p306 m) : NeverHalts m :=
  zipCycle_sound p306 3 6 true (1) (by decide) cert306 m hm
#print axioms never306


/-- Third-level first-hole refinement 307, 1RB0RE_1RC0RA_0RD---_1LD1RB_1RD---_------; entry 0, period 12. -/
def p307 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert307 : zipCycle p307 0 12 true (0) = true := by decide +kernel
theorem never307 (m : Machine) (hm : compatible p307 m) : NeverHalts m :=
  zipCycle_sound p307 0 12 true (0) (by decide) cert307 m hm
#print axioms never307


/-- Third-level first-hole refinement 308, 1RB0RE_1RC0RA_0RD---_1LD1RB_0RE---_------; entry 8, period 1. -/
def p308 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert308 : zipCycle p308 8 1 true (4) = true := by decide +kernel
theorem never308 (m : Machine) (hm : compatible p308 m) : NeverHalts m :=
  zipCycle_sound p308 8 1 true (4) (by decide) cert308 m hm
#print axioms never308


/-- Third-level first-hole refinement 309, 1RB0RE_1RC0RA_0RD---_1LD1RB_1RE---_------; entry 8, period 1. -/
def p309 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert309 : zipCycle p309 8 1 true (4) = true := by decide +kernel
theorem never309 (m : Machine) (hm : compatible p309 m) : NeverHalts m :=
  zipCycle_sound p309 8 1 true (4) (by decide) cert309 m hm
#print axioms never309


/-- Third-level first-hole refinement 310, 1RB1RE_1RC0RA_0RD---_1LD1RB_0LA---_------; entry 7, period 2. -/
def p310 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert310 : zipCycle p310 7 2 true (3) = true := by decide +kernel
theorem never310 (m : Machine) (hm : compatible p310 m) : NeverHalts m :=
  zipCycle_sound p310 7 2 true (3) (by decide) cert310 m hm
#print axioms never310


/-- Third-level first-hole refinement 311, 1RB1RE_1RC0RA_0RD---_1LD1RB_0RA---_------; entry 0, period 9. -/
def p311 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert311 : zipCycle p311 0 9 true (0) = true := by decide +kernel
theorem never311 (m : Machine) (hm : compatible p311 m) : NeverHalts m :=
  zipCycle_sound p311 0 9 true (0) (by decide) cert311 m hm
#print axioms never311


/-- Third-level first-hole refinement 312, 1RB1RE_1RC0RA_0RD---_1LD1RB_1RA---_------; entry 0, period 9. -/
def p312 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert312 : zipCycle p312 0 9 true (0) = true := by decide +kernel
theorem never312 (m : Machine) (hm : compatible p312 m) : NeverHalts m :=
  zipCycle_sound p312 0 9 true (0) (by decide) cert312 m hm
#print axioms never312


/-- Third-level first-hole refinement 313, 1RB1RE_1RC0RA_0RD---_1LD1RB_0LB---_------; entry 0, period 10. -/
def p313 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert313 : zipCycle p313 0 10 true (0) = true := by decide +kernel
theorem never313 (m : Machine) (hm : compatible p313 m) : NeverHalts m :=
  zipCycle_sound p313 0 10 true (0) (by decide) cert313 m hm
#print axioms never313


/-- Third-level first-hole refinement 314, 1RB1RE_1RC0RA_0RD---_1LD1RB_1LB---_------; entry 6, period 3. -/
def p314 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert314 : zipCycle p314 6 3 true (2) = true := by decide +kernel
theorem never314 (m : Machine) (hm : compatible p314 m) : NeverHalts m :=
  zipCycle_sound p314 6 3 true (2) (by decide) cert314 m hm
#print axioms never314


/-- Third-level first-hole refinement 315, 1RB1RE_1RC0RA_0RD---_1LD1RB_0RB---_------; entry 1, period 8. -/
def p315 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert315 : zipCycle p315 1 8 true (1) = true := by decide +kernel
theorem never315 (m : Machine) (hm : compatible p315 m) : NeverHalts m :=
  zipCycle_sound p315 1 8 true (1) (by decide) cert315 m hm
#print axioms never315


/-- Third-level first-hole refinement 316, 1RB1RE_1RC0RA_0RD---_1LD1RB_1RB---_------; entry 1, period 8. -/
def p316 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert316 : zipCycle p316 1 8 true (1) = true := by decide +kernel
theorem never316 (m : Machine) (hm : compatible p316 m) : NeverHalts m :=
  zipCycle_sound p316 1 8 true (1) (by decide) cert316 m hm
#print axioms never316


/-- Third-level first-hole refinement 317, 1RB1RE_1RC0RA_0RD---_1LD1RB_1RC---_------; entry 2, period 7. -/
def p317 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert317 : zipCycle p317 2 7 true (1) = true := by decide +kernel
theorem never317 (m : Machine) (hm : compatible p317 m) : NeverHalts m :=
  zipCycle_sound p317 2 7 true (1) (by decide) cert317 m hm
#print axioms never317


/-- Third-level first-hole refinement 318, 1RB1RE_1RC0RA_0RD---_1LD1RB_0LD---_------; entry 1, period 9. -/
def p318 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert318 : zipCycle p318 1 9 true (1) = true := by decide +kernel
theorem never318 (m : Machine) (hm : compatible p318 m) : NeverHalts m :=
  zipCycle_sound p318 1 9 true (1) (by decide) cert318 m hm
#print axioms never318


/-- Third-level first-hole refinement 319, 1RB1RE_1RC0RA_0RD---_1LD1RB_1LD---_------; entry 0, period 11. -/
def p319 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert319 : zipCycle p319 0 11 true (0) = true := by decide +kernel
theorem never319 (m : Machine) (hm : compatible p319 m) : NeverHalts m :=
  zipCycle_sound p319 0 11 true (0) (by decide) cert319 m hm
#print axioms never319


/-- Third-level first-hole refinement 320, 1RB1RE_1RC0RA_0RD---_1LD1RB_0RD---_------; entry 3, period 6. -/
def p320 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert320 : zipCycle p320 3 6 true (1) = true := by decide +kernel
theorem never320 (m : Machine) (hm : compatible p320 m) : NeverHalts m :=
  zipCycle_sound p320 3 6 true (1) (by decide) cert320 m hm
#print axioms never320


/-- Third-level first-hole refinement 321, 1RB1RE_1RC0RA_0RD---_1LD1RB_1RD---_------; entry 0, period 12. -/
def p321 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert321 : zipCycle p321 0 12 true (0) = true := by decide +kernel
theorem never321 (m : Machine) (hm : compatible p321 m) : NeverHalts m :=
  zipCycle_sound p321 0 12 true (0) (by decide) cert321 m hm
#print axioms never321


/-- Third-level first-hole refinement 322, 1RB1RE_1RC0RA_0RD---_1LD1RB_0RE---_------; entry 8, period 1. -/
def p322 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert322 : zipCycle p322 8 1 true (4) = true := by decide +kernel
theorem never322 (m : Machine) (hm : compatible p322 m) : NeverHalts m :=
  zipCycle_sound p322 8 1 true (4) (by decide) cert322 m hm
#print axioms never322


/-- Third-level first-hole refinement 323, 1RB1RE_1RC0RA_0RD---_1LD1RB_1RE---_------; entry 8, period 1. -/
def p323 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert323 : zipCycle p323 8 1 true (4) = true := by decide +kernel
theorem never323 (m : Machine) (hm : compatible p323 m) : NeverHalts m :=
  zipCycle_sound p323 8 1 true (4) (by decide) cert323 m hm
#print axioms never323


/-- Third-level first-hole refinement 324, 1RB0LC_1RC1RA_0RD0LA_1LD1RB_------_------; entry 0, period 11. -/
def p324 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert324 : zipCycle p324 0 11 false (3) = true := by decide +kernel
theorem never324 (m : Machine) (hm : compatible p324 m) : NeverHalts m :=
  zipCycle_sound p324 0 11 false (3) (by decide) cert324 m hm
#print axioms never324


/-- Third-level first-hole refinement 325, 1RB0LC_1RC1RA_0RD0RA_1LD1RB_------_------; entry 0, period 9. -/
def p325 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert325 : zipCycle p325 0 9 true (0) = true := by decide +kernel
theorem never325 (m : Machine) (hm : compatible p325 m) : NeverHalts m :=
  zipCycle_sound p325 0 9 true (0) (by decide) cert325 m hm
#print axioms never325


/-- Third-level first-hole refinement 326, 1RB0LC_1RC1RA_0RD1RA_1LD1RB_------_------; entry 0, period 9. -/
def p326 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert326 : zipCycle p326 0 9 true (0) = true := by decide +kernel
theorem never326 (m : Machine) (hm : compatible p326 m) : NeverHalts m :=
  zipCycle_sound p326 0 9 true (0) (by decide) cert326 m hm
#print axioms never326


/-- Third-level first-hole refinement 327, 1RB0LC_1RC1RA_0RD0LB_1LD1RB_------_------; entry 0, period 10. -/
def p327 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert327 : zipCycle p327 0 10 true (0) = true := by decide +kernel
theorem never327 (m : Machine) (hm : compatible p327 m) : NeverHalts m :=
  zipCycle_sound p327 0 10 true (0) (by decide) cert327 m hm
#print axioms never327


/-- Third-level first-hole refinement 328, 1RB0LC_1RC1RA_0RD1LB_1LD1RB_------_------; entry 11, period 5. -/
def p328 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert328 : zipCycle p328 11 5 false (1) = true := by decide +kernel
theorem never328 (m : Machine) (hm : compatible p328 m) : NeverHalts m :=
  zipCycle_sound p328 11 5 false (1) (by decide) cert328 m hm
#print axioms never328


/-- Third-level first-hole refinement 329, 1RB0LC_1RC1RA_0RD0RB_1LD1RB_------_------; entry 1, period 8. -/
def p329 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert329 : zipCycle p329 1 8 true (1) = true := by decide +kernel
theorem never329 (m : Machine) (hm : compatible p329 m) : NeverHalts m :=
  zipCycle_sound p329 1 8 true (1) (by decide) cert329 m hm
#print axioms never329


/-- Third-level first-hole refinement 330, 1RB0LC_1RC1RA_0RD1RB_1LD1RB_------_------; entry 1, period 8. -/
def p330 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert330 : zipCycle p330 1 8 true (1) = true := by decide +kernel
theorem never330 (m : Machine) (hm : compatible p330 m) : NeverHalts m :=
  zipCycle_sound p330 1 8 true (1) (by decide) cert330 m hm
#print axioms never330


/-- Third-level first-hole refinement 331, 1RB0LC_1RC1RA_0RD0LC_1LD1RB_------_------; entry 12, period 1. -/
def p331 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert331 : zipCycle p331 12 1 false (0) = true := by decide +kernel
theorem never331 (m : Machine) (hm : compatible p331 m) : NeverHalts m :=
  zipCycle_sound p331 12 1 false (0) (by decide) cert331 m hm
#print axioms never331


/-- Third-level first-hole refinement 332, 1RB0LC_1RC1RA_0RD0RC_1LD1RB_------_------; entry 1, period 18. -/
def p332 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert332 : zipCycle p332 1 18 true (1) = true := by decide +kernel
theorem never332 (m : Machine) (hm : compatible p332 m) : NeverHalts m :=
  zipCycle_sound p332 1 18 true (1) (by decide) cert332 m hm
#print axioms never332


/-- Third-level first-hole refinement 333, 1RB0LC_1RC1RA_0RD1RC_1LD1RB_------_------; entry 2, period 7. -/
def p333 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert333 : zipCycle p333 2 7 true (1) = true := by decide +kernel
theorem never333 (m : Machine) (hm : compatible p333 m) : NeverHalts m :=
  zipCycle_sound p333 2 7 true (1) (by decide) cert333 m hm
#print axioms never333


/-- Third-level first-hole refinement 334, 1RB0LC_1RC1RA_0RD0LD_1LD1RB_------_------; entry 1, period 9. -/
def p334 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert334 : zipCycle p334 1 9 true (1) = true := by decide +kernel
theorem never334 (m : Machine) (hm : compatible p334 m) : NeverHalts m :=
  zipCycle_sound p334 1 9 true (1) (by decide) cert334 m hm
#print axioms never334


/-- Third-level first-hole refinement 335, 1RB0LC_1RC1RA_0RD1LD_1LD1RB_------_------; entry 0, period 11. -/
def p335 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert335 : zipCycle p335 0 11 true (0) = true := by decide +kernel
theorem never335 (m : Machine) (hm : compatible p335 m) : NeverHalts m :=
  zipCycle_sound p335 0 11 true (0) (by decide) cert335 m hm
#print axioms never335


/-- Third-level first-hole refinement 336, 1RB0LC_1RC1RA_0RD0RD_1LD1RB_------_------; entry 3, period 6. -/
def p336 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert336 : zipCycle p336 3 6 true (1) = true := by decide +kernel
theorem never336 (m : Machine) (hm : compatible p336 m) : NeverHalts m :=
  zipCycle_sound p336 3 6 true (1) (by decide) cert336 m hm
#print axioms never336


/-- Third-level first-hole refinement 337, 1RB0LC_1RC1RA_0RD1RD_1LD1RB_------_------; entry 0, period 12. -/
def p337 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert337 : zipCycle p337 0 12 true (0) = true := by decide +kernel
theorem never337 (m : Machine) (hm : compatible p337 m) : NeverHalts m :=
  zipCycle_sound p337 0 12 true (0) (by decide) cert337 m hm
#print axioms never337


/-- Third-level first-hole refinement 338, 1RB1LC_1RC1RA_0RD0LA_1LD1RB_------_------; entry 8, period 5. -/
def p338 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert338 : zipCycle p338 8 5 false (2) = true := by decide +kernel
theorem never338 (m : Machine) (hm : compatible p338 m) : NeverHalts m :=
  zipCycle_sound p338 8 5 false (2) (by decide) cert338 m hm
#print axioms never338


/-- Third-level first-hole refinement 339, 1RB1LC_1RC1RA_0RD1LA_1LD1RB_------_------; entry 12, period 6. -/
def p339 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert339 : zipCycle p339 12 6 true (-2) = true := by decide +kernel
theorem never339 (m : Machine) (hm : compatible p339 m) : NeverHalts m :=
  zipCycle_sound p339 12 6 true (-2) (by decide) cert339 m hm
#print axioms never339


/-- Third-level first-hole refinement 340, 1RB1LC_1RC1RA_0RD0RA_1LD1RB_------_------; entry 1, period 11. -/
def p340 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert340 : zipCycle p340 1 11 true (1) = true := by decide +kernel
theorem never340 (m : Machine) (hm : compatible p340 m) : NeverHalts m :=
  zipCycle_sound p340 1 11 true (1) (by decide) cert340 m hm
#print axioms never340


/-- Third-level first-hole refinement 341, 1RB1LC_1RC1RA_0RD1RA_1LD1RB_------_------; entry 7, period 2. -/
def p341 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert341 : zipCycle p341 7 2 true (2) = true := by decide +kernel
theorem never341 (m : Machine) (hm : compatible p341 m) : NeverHalts m :=
  zipCycle_sound p341 7 2 true (2) (by decide) cert341 m hm
#print axioms never341


/-- Third-level first-hole refinement 342, 1RB1LC_1RC1RA_0RD0LB_1LD1RB_------_------; entry 0, period 12. -/
def p342 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert342 : zipCycle p342 0 12 true (0) = true := by decide +kernel
theorem never342 (m : Machine) (hm : compatible p342 m) : NeverHalts m :=
  zipCycle_sound p342 0 12 true (0) (by decide) cert342 m hm
#print axioms never342


/-- Third-level first-hole refinement 343, 1RB1LC_1RC1RA_0RD1LB_1LD1RB_------_------; entry 11, period 5. -/
def p343 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert343 : zipCycle p343 11 5 false (1) = true := by decide +kernel
theorem never343 (m : Machine) (hm : compatible p343 m) : NeverHalts m :=
  zipCycle_sound p343 11 5 false (1) (by decide) cert343 m hm
#print axioms never343


/-- Third-level first-hole refinement 344, 1RB1LC_1RC1RA_0RD0RB_1LD1RB_------_------; entry 0, period 10. -/
def p344 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert344 : zipCycle p344 0 10 true (0) = true := by decide +kernel
theorem never344 (m : Machine) (hm : compatible p344 m) : NeverHalts m :=
  zipCycle_sound p344 0 10 true (0) (by decide) cert344 m hm
#print axioms never344


/-- Third-level first-hole refinement 345, 1RB1LC_1RC1RA_0RD1RB_1LD1RB_------_------; entry 0, period 10. -/
def p345 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert345 : zipCycle p345 0 10 true (0) = true := by decide +kernel
theorem never345 (m : Machine) (hm : compatible p345 m) : NeverHalts m :=
  zipCycle_sound p345 0 10 true (0) (by decide) cert345 m hm
#print axioms never345


/-- Third-level first-hole refinement 346, 1RB1LC_1RC1RA_0RD0LC_1LD1RB_------_------; entry 12, period 1. -/
def p346 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert346 : zipCycle p346 12 1 false (0) = true := by decide +kernel
theorem never346 (m : Machine) (hm : compatible p346 m) : NeverHalts m :=
  zipCycle_sound p346 12 1 false (0) (by decide) cert346 m hm
#print axioms never346


/-- Third-level first-hole refinement 347, 1RB1LC_1RC1RA_0RD1LC_1LD1RB_------_------; entry 9, period 6. -/
def p347 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert347 : zipCycle p347 9 6 true (-1) = true := by decide +kernel
theorem never347 (m : Machine) (hm : compatible p347 m) : NeverHalts m :=
  zipCycle_sound p347 9 6 true (-1) (by decide) cert347 m hm
#print axioms never347


/-- Third-level first-hole refinement 348, 1RB1LC_1RC1RA_0RD1RC_1LD1RB_------_------; entry 2, period 8. -/
def p348 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert348 : zipCycle p348 2 8 true (1) = true := by decide +kernel
theorem never348 (m : Machine) (hm : compatible p348 m) : NeverHalts m :=
  zipCycle_sound p348 2 8 true (1) (by decide) cert348 m hm
#print axioms never348


/-- Third-level first-hole refinement 349, 1RB1LC_1RC1RA_0RD0LD_1LD1RB_------_------; entry 1, period 12. -/
def p349 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert349 : zipCycle p349 1 12 true (1) = true := by decide +kernel
theorem never349 (m : Machine) (hm : compatible p349 m) : NeverHalts m :=
  zipCycle_sound p349 1 12 true (1) (by decide) cert349 m hm
#print axioms never349


/-- Third-level first-hole refinement 350, 1RB1LC_1RC1RA_0RD1LD_1LD1RB_------_------; entry 5, period 4. -/
def p350 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert350 : zipCycle p350 5 4 true (1) = true := by decide +kernel
theorem never350 (m : Machine) (hm : compatible p350 m) : NeverHalts m :=
  zipCycle_sound p350 5 4 true (1) (by decide) cert350 m hm
#print axioms never350


/-- Third-level first-hole refinement 351, 1RB1LC_1RC1RA_0RD0RD_1LD1RB_------_------; entry 1, period 9. -/
def p351 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert351 : zipCycle p351 1 9 true (1) = true := by decide +kernel
theorem never351 (m : Machine) (hm : compatible p351 m) : NeverHalts m :=
  zipCycle_sound p351 1 9 true (1) (by decide) cert351 m hm
#print axioms never351


/-- Third-level first-hole refinement 352, 1RB1LC_1RC1RA_0RD1RD_1LD1RB_------_------; entry 1, period 9. -/
def p352 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert352 : zipCycle p352 1 9 true (1) = true := by decide +kernel
theorem never352 (m : Machine) (hm : compatible p352 m) : NeverHalts m :=
  zipCycle_sound p352 1 9 true (1) (by decide) cert352 m hm
#print axioms never352


/-- Third-level first-hole refinement 353, 1RB0RC_1RC1RA_0RD0LA_1LD1RB_------_------; entry 0, period 16. -/
def p353 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert353 : zipCycle p353 0 16 true (0) = true := by decide +kernel
theorem never353 (m : Machine) (hm : compatible p353 m) : NeverHalts m :=
  zipCycle_sound p353 0 16 true (0) (by decide) cert353 m hm
#print axioms never353


/-- Third-level first-hole refinement 354, 1RB0RC_1RC1RA_0RD1LA_1LD1RB_------_------; entry 0, period 18. -/
def p354 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert354 : zipCycle p354 0 18 true (0) = true := by decide +kernel
theorem never354 (m : Machine) (hm : compatible p354 m) : NeverHalts m :=
  zipCycle_sound p354 0 18 true (0) (by decide) cert354 m hm
#print axioms never354


/-- Third-level first-hole refinement 355, 1RB0RC_1RC1RA_0RD0RA_1LD1RB_------_------; entry 0, period 16. -/
def p355 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert355 : zipCycle p355 0 16 true (0) = true := by decide +kernel
theorem never355 (m : Machine) (hm : compatible p355 m) : NeverHalts m :=
  zipCycle_sound p355 0 16 true (0) (by decide) cert355 m hm
#print axioms never355


/-- Third-level first-hole refinement 356, 1RB0RC_1RC1RA_0RD1RA_1LD1RB_------_------; entry 0, period 16. -/
def p356 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert356 : zipCycle p356 0 16 true (0) = true := by decide +kernel
theorem never356 (m : Machine) (hm : compatible p356 m) : NeverHalts m :=
  zipCycle_sound p356 0 16 true (0) (by decide) cert356 m hm
#print axioms never356


/-- Third-level first-hole refinement 357, 1RB0RC_1RC1RA_0RD0LB_1LD1RB_------_------; entry 1, period 15. -/
def p357 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert357 : zipCycle p357 1 15 true (1) = true := by decide +kernel
theorem never357 (m : Machine) (hm : compatible p357 m) : NeverHalts m :=
  zipCycle_sound p357 1 15 true (1) (by decide) cert357 m hm
#print axioms never357


/-- Third-level first-hole refinement 358, 1RB0RC_1RC1RA_0RD1LB_1LD1RB_------_------; entry 6, period 12. -/
def p358 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert358 : zipCycle p358 6 12 true (2) = true := by decide +kernel
theorem never358 (m : Machine) (hm : compatible p358 m) : NeverHalts m :=
  zipCycle_sound p358 6 12 true (2) (by decide) cert358 m hm
#print axioms never358


/-- Third-level first-hole refinement 359, 1RB0RC_1RC1RA_0RD0RB_1LD1RB_------_------; entry 1, period 15. -/
def p359 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert359 : zipCycle p359 1 15 true (1) = true := by decide +kernel
theorem never359 (m : Machine) (hm : compatible p359 m) : NeverHalts m :=
  zipCycle_sound p359 1 15 true (1) (by decide) cert359 m hm
#print axioms never359


/-- Third-level first-hole refinement 360, 1RB0RC_1RC1RA_0RD1RB_1LD1RB_------_------; entry 1, period 15. -/
def p360 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert360 : zipCycle p360 1 15 true (1) = true := by decide +kernel
theorem never360 (m : Machine) (hm : compatible p360 m) : NeverHalts m :=
  zipCycle_sound p360 1 15 true (1) (by decide) cert360 m hm
#print axioms never360


/-- Third-level first-hole refinement 361, 1RB0RC_1RC1RA_0RD0LC_1LD1RB_------_------; entry 2, period 14. -/
def p361 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert361 : zipCycle p361 2 14 true (1) = true := by decide +kernel
theorem never361 (m : Machine) (hm : compatible p361 m) : NeverHalts m :=
  zipCycle_sound p361 2 14 true (1) (by decide) cert361 m hm
#print axioms never361


/-- Third-level first-hole refinement 362, 1RB0RC_1RC1RA_0RD1LC_1LD1RB_------_------; entry 1, period 17. -/
def p362 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert362 : zipCycle p362 1 17 true (1) = true := by decide +kernel
theorem never362 (m : Machine) (hm : compatible p362 m) : NeverHalts m :=
  zipCycle_sound p362 1 17 true (1) (by decide) cert362 m hm
#print axioms never362


/-- Third-level first-hole refinement 363, 1RB0RC_1RC1RA_0RD1RC_1LD1RB_------_------; entry 2, period 14. -/
def p363 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert363 : zipCycle p363 2 14 true (1) = true := by decide +kernel
theorem never363 (m : Machine) (hm : compatible p363 m) : NeverHalts m :=
  zipCycle_sound p363 2 14 true (1) (by decide) cert363 m hm
#print axioms never363


/-- Third-level first-hole refinement 364, 1RB0RC_1RC1RA_0RD0LD_1LD1RB_------_------; entry 0, period 19. -/
def p364 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert364 : zipCycle p364 0 19 true (0) = true := by decide +kernel
theorem never364 (m : Machine) (hm : compatible p364 m) : NeverHalts m :=
  zipCycle_sound p364 0 19 true (0) (by decide) cert364 m hm
#print axioms never364


/-- Third-level first-hole refinement 365, 1RB0RC_1RC1RA_0RD1LD_1LD1RB_------_------; entry 4, period 12. -/
def p365 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert365 : zipCycle p365 4 12 true (1) = true := by decide +kernel
theorem never365 (m : Machine) (hm : compatible p365 m) : NeverHalts m :=
  zipCycle_sound p365 4 12 true (1) (by decide) cert365 m hm
#print axioms never365


/-- Third-level first-hole refinement 366, 1RB0RC_1RC1RA_0RD0RD_1LD1RB_------_------; entry 9, period 7. -/
def p366 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert366 : zipCycle p366 9 7 true (2) = true := by decide +kernel
theorem never366 (m : Machine) (hm : compatible p366 m) : NeverHalts m :=
  zipCycle_sound p366 9 7 true (2) (by decide) cert366 m hm
#print axioms never366


/-- Third-level first-hole refinement 367, 1RB0RC_1RC1RA_0RD1RD_1LD1RB_------_------; entry 0, period 19. -/
def p367 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert367 : zipCycle p367 0 19 true (0) = true := by decide +kernel
theorem never367 (m : Machine) (hm : compatible p367 m) : NeverHalts m :=
  zipCycle_sound p367 0 19 true (0) (by decide) cert367 m hm
#print axioms never367


/-- Third-level first-hole refinement 368, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0LA_------; entry 0, period 11. -/
def p368 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert368 : zipCycle p368 0 11 false (3) = true := by decide +kernel
theorem never368 (m : Machine) (hm : compatible p368 m) : NeverHalts m :=
  zipCycle_sound p368 0 11 false (3) (by decide) cert368 m hm
#print axioms never368


/-- Third-level first-hole refinement 369, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0RA_------; entry 0, period 9. -/
def p369 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert369 : zipCycle p369 0 9 true (0) = true := by decide +kernel
theorem never369 (m : Machine) (hm : compatible p369 m) : NeverHalts m :=
  zipCycle_sound p369 0 9 true (0) (by decide) cert369 m hm
#print axioms never369


/-- Third-level first-hole refinement 370, 1RB0LE_1RC1RA_0RD---_1LD1RB_---1RA_------; entry 0, period 9. -/
def p370 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert370 : zipCycle p370 0 9 true (0) = true := by decide +kernel
theorem never370 (m : Machine) (hm : compatible p370 m) : NeverHalts m :=
  zipCycle_sound p370 0 9 true (0) (by decide) cert370 m hm
#print axioms never370


/-- Third-level first-hole refinement 371, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0LB_------; entry 0, period 10. -/
def p371 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert371 : zipCycle p371 0 10 true (0) = true := by decide +kernel
theorem never371 (m : Machine) (hm : compatible p371 m) : NeverHalts m :=
  zipCycle_sound p371 0 10 true (0) (by decide) cert371 m hm
#print axioms never371


/-- Third-level first-hole refinement 372, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0RB_------; entry 1, period 8. -/
def p372 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert372 : zipCycle p372 1 8 true (1) = true := by decide +kernel
theorem never372 (m : Machine) (hm : compatible p372 m) : NeverHalts m :=
  zipCycle_sound p372 1 8 true (1) (by decide) cert372 m hm
#print axioms never372


/-- Third-level first-hole refinement 373, 1RB0LE_1RC1RA_0RD---_1LD1RB_---1RB_------; entry 1, period 8. -/
def p373 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert373 : zipCycle p373 1 8 true (1) = true := by decide +kernel
theorem never373 (m : Machine) (hm : compatible p373 m) : NeverHalts m :=
  zipCycle_sound p373 1 8 true (1) (by decide) cert373 m hm
#print axioms never373


/-- Third-level first-hole refinement 374, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0RC_------; entry 1, period 18. -/
def p374 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert374 : zipCycle p374 1 18 true (1) = true := by decide +kernel
theorem never374 (m : Machine) (hm : compatible p374 m) : NeverHalts m :=
  zipCycle_sound p374 1 18 true (1) (by decide) cert374 m hm
#print axioms never374


/-- Third-level first-hole refinement 375, 1RB0LE_1RC1RA_0RD---_1LD1RB_---1RC_------; entry 2, period 7. -/
def p375 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert375 : zipCycle p375 2 7 true (1) = true := by decide +kernel
theorem never375 (m : Machine) (hm : compatible p375 m) : NeverHalts m :=
  zipCycle_sound p375 2 7 true (1) (by decide) cert375 m hm
#print axioms never375


/-- Third-level first-hole refinement 376, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0LD_------; entry 1, period 9. -/
def p376 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert376 : zipCycle p376 1 9 true (1) = true := by decide +kernel
theorem never376 (m : Machine) (hm : compatible p376 m) : NeverHalts m :=
  zipCycle_sound p376 1 9 true (1) (by decide) cert376 m hm
#print axioms never376


/-- Third-level first-hole refinement 377, 1RB0LE_1RC1RA_0RD---_1LD1RB_---1LD_------; entry 0, period 11. -/
def p377 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert377 : zipCycle p377 0 11 true (0) = true := by decide +kernel
theorem never377 (m : Machine) (hm : compatible p377 m) : NeverHalts m :=
  zipCycle_sound p377 0 11 true (0) (by decide) cert377 m hm
#print axioms never377


/-- Third-level first-hole refinement 378, 1RB0LE_1RC1RA_0RD---_1LD1RB_---0RD_------; entry 3, period 6. -/
def p378 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert378 : zipCycle p378 3 6 true (1) = true := by decide +kernel
theorem never378 (m : Machine) (hm : compatible p378 m) : NeverHalts m :=
  zipCycle_sound p378 3 6 true (1) (by decide) cert378 m hm
#print axioms never378


/-- Third-level first-hole refinement 379, 1RB0LE_1RC1RA_0RD---_1LD1RB_---1RD_------; entry 0, period 12. -/
def p379 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert379 : zipCycle p379 0 12 true (0) = true := by decide +kernel
theorem never379 (m : Machine) (hm : compatible p379 m) : NeverHalts m :=
  zipCycle_sound p379 0 12 true (0) (by decide) cert379 m hm
#print axioms never379


/-- Third-level first-hole refinement 380, 1RB1LE_1RC1RA_0RD---_1LD1RB_---1RA_------; entry 7, period 2. -/
def p380 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert380 : zipCycle p380 7 2 true (2) = true := by decide +kernel
theorem never380 (m : Machine) (hm : compatible p380 m) : NeverHalts m :=
  zipCycle_sound p380 7 2 true (2) (by decide) cert380 m hm
#print axioms never380


/-- Third-level first-hole refinement 381, 1RB1LE_1RC1RA_0RD---_1LD1RB_---0LB_------; entry 0, period 12. -/
def p381 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert381 : zipCycle p381 0 12 true (0) = true := by decide +kernel
theorem never381 (m : Machine) (hm : compatible p381 m) : NeverHalts m :=
  zipCycle_sound p381 0 12 true (0) (by decide) cert381 m hm
#print axioms never381


/-- Third-level first-hole refinement 382, 1RB1LE_1RC1RA_0RD---_1LD1RB_---0RB_------; entry 0, period 10. -/
def p382 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert382 : zipCycle p382 0 10 true (0) = true := by decide +kernel
theorem never382 (m : Machine) (hm : compatible p382 m) : NeverHalts m :=
  zipCycle_sound p382 0 10 true (0) (by decide) cert382 m hm
#print axioms never382


/-- Third-level first-hole refinement 383, 1RB1LE_1RC1RA_0RD---_1LD1RB_---1RB_------; entry 0, period 10. -/
def p383 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert383 : zipCycle p383 0 10 true (0) = true := by decide +kernel
theorem never383 (m : Machine) (hm : compatible p383 m) : NeverHalts m :=
  zipCycle_sound p383 0 10 true (0) (by decide) cert383 m hm
#print axioms never383


/-- Third-level first-hole refinement 384, 1RB1LE_1RC1RA_0RD---_1LD1RB_---1LD_------; entry 5, period 4. -/
def p384 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert384 : zipCycle p384 5 4 true (1) = true := by decide +kernel
theorem never384 (m : Machine) (hm : compatible p384 m) : NeverHalts m :=
  zipCycle_sound p384 5 4 true (1) (by decide) cert384 m hm
#print axioms never384


/-- Third-level first-hole refinement 385, 1RB1LE_1RC1RA_0RD---_1LD1RB_---0RD_------; entry 1, period 9. -/
def p385 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert385 : zipCycle p385 1 9 true (1) = true := by decide +kernel
theorem never385 (m : Machine) (hm : compatible p385 m) : NeverHalts m :=
  zipCycle_sound p385 1 9 true (1) (by decide) cert385 m hm
#print axioms never385


/-- Third-level first-hole refinement 386, 1RB1LE_1RC1RA_0RD---_1LD1RB_---1RD_------; entry 1, period 9. -/
def p386 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert386 : zipCycle p386 1 9 true (1) = true := by decide +kernel
theorem never386 (m : Machine) (hm : compatible p386 m) : NeverHalts m :=
  zipCycle_sound p386 1 9 true (1) (by decide) cert386 m hm
#print axioms never386


/-- Third-level first-hole refinement 387, 1RB0RE_1RC1RA_0RD---_1LD1RB_0LA---_------; entry 0, period 9. -/
def p387 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert387 : zipCycle p387 0 9 true (0) = true := by decide +kernel
theorem never387 (m : Machine) (hm : compatible p387 m) : NeverHalts m :=
  zipCycle_sound p387 0 9 true (0) (by decide) cert387 m hm
#print axioms never387


/-- Third-level first-hole refinement 388, 1RB0RE_1RC1RA_0RD---_1LD1RB_1LA---_------; entry 0, period 11. -/
def p388 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert388 : zipCycle p388 0 11 true (0) = true := by decide +kernel
theorem never388 (m : Machine) (hm : compatible p388 m) : NeverHalts m :=
  zipCycle_sound p388 0 11 true (0) (by decide) cert388 m hm
#print axioms never388


/-- Third-level first-hole refinement 389, 1RB0RE_1RC1RA_0RD---_1LD1RB_0RA---_------; entry 0, period 9. -/
def p389 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert389 : zipCycle p389 0 9 true (0) = true := by decide +kernel
theorem never389 (m : Machine) (hm : compatible p389 m) : NeverHalts m :=
  zipCycle_sound p389 0 9 true (0) (by decide) cert389 m hm
#print axioms never389


/-- Third-level first-hole refinement 390, 1RB0RE_1RC1RA_0RD---_1LD1RB_1RA---_------; entry 0, period 9. -/
def p390 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert390 : zipCycle p390 0 9 true (0) = true := by decide +kernel
theorem never390 (m : Machine) (hm : compatible p390 m) : NeverHalts m :=
  zipCycle_sound p390 0 9 true (0) (by decide) cert390 m hm
#print axioms never390


/-- Third-level first-hole refinement 391, 1RB0RE_1RC1RA_0RD---_1LD1RB_0LB---_------; entry 1, period 8. -/
def p391 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert391 : zipCycle p391 1 8 true (1) = true := by decide +kernel
theorem never391 (m : Machine) (hm : compatible p391 m) : NeverHalts m :=
  zipCycle_sound p391 1 8 true (1) (by decide) cert391 m hm
#print axioms never391


/-- Third-level first-hole refinement 392, 1RB0RE_1RC1RA_0RD---_1LD1RB_0RB---_------; entry 1, period 8. -/
def p392 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert392 : zipCycle p392 1 8 true (1) = true := by decide +kernel
theorem never392 (m : Machine) (hm : compatible p392 m) : NeverHalts m :=
  zipCycle_sound p392 1 8 true (1) (by decide) cert392 m hm
#print axioms never392


/-- Third-level first-hole refinement 393, 1RB0RE_1RC1RA_0RD---_1LD1RB_1RB---_------; entry 1, period 8. -/
def p393 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert393 : zipCycle p393 1 8 true (1) = true := by decide +kernel
theorem never393 (m : Machine) (hm : compatible p393 m) : NeverHalts m :=
  zipCycle_sound p393 1 8 true (1) (by decide) cert393 m hm
#print axioms never393


/-- Third-level first-hole refinement 394, 1RB0RE_1RC1RA_0RD---_1LD1RB_0LC---_------; entry 2, period 7. -/
def p394 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert394 : zipCycle p394 2 7 true (1) = true := by decide +kernel
theorem never394 (m : Machine) (hm : compatible p394 m) : NeverHalts m :=
  zipCycle_sound p394 2 7 true (1) (by decide) cert394 m hm
#print axioms never394


/-- Third-level first-hole refinement 395, 1RB0RE_1RC1RA_0RD---_1LD1RB_1LC---_------; entry 1, period 10. -/
def p395 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert395 : zipCycle p395 1 10 true (1) = true := by decide +kernel
theorem never395 (m : Machine) (hm : compatible p395 m) : NeverHalts m :=
  zipCycle_sound p395 1 10 true (1) (by decide) cert395 m hm
#print axioms never395


/-- Third-level first-hole refinement 396, 1RB0RE_1RC1RA_0RD---_1LD1RB_1RC---_------; entry 2, period 7. -/
def p396 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert396 : zipCycle p396 2 7 true (1) = true := by decide +kernel
theorem never396 (m : Machine) (hm : compatible p396 m) : NeverHalts m :=
  zipCycle_sound p396 2 7 true (1) (by decide) cert396 m hm
#print axioms never396


/-- Third-level first-hole refinement 397, 1RB0RE_1RC1RA_0RD---_1LD1RB_0LD---_------; entry 0, period 12. -/
def p397 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert397 : zipCycle p397 0 12 true (0) = true := by decide +kernel
theorem never397 (m : Machine) (hm : compatible p397 m) : NeverHalts m :=
  zipCycle_sound p397 0 12 true (0) (by decide) cert397 m hm
#print axioms never397


/-- Third-level first-hole refinement 398, 1RB0RE_1RC1RA_0RD---_1LD1RB_1LD---_------; entry 4, period 5. -/
def p398 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert398 : zipCycle p398 4 5 true (1) = true := by decide +kernel
theorem never398 (m : Machine) (hm : compatible p398 m) : NeverHalts m :=
  zipCycle_sound p398 4 5 true (1) (by decide) cert398 m hm
#print axioms never398


/-- Third-level first-hole refinement 399, 1RB0RE_1RC1RA_0RD---_1LD1RB_1RD---_------; entry 0, period 12. -/
def p399 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,0⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert399 : zipCycle p399 0 12 true (0) = true := by decide +kernel
theorem never399 (m : Machine) (hm : compatible p399 m) : NeverHalts m :=
  zipCycle_sound p399 0 12 true (0) (by decide) cert399 m hm
#print axioms never399

end BB6.Agent24Raw45D3_03
