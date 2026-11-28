import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_07
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 700, 1RB---_1RC0RC_0RD0RE_1LD1RB_1LB---_------; entry 7, period 3. -/
def p700 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert700 : zipCycle p700 7 3 true (3) = true := by decide +kernel
theorem never700 (m : Machine) (hm : compatible p700 m) : NeverHalts m :=
  zipCycle_sound p700 7 3 true (3) (by decide) cert700 m hm
#print axioms never700


/-- Third-level first-hole refinement 701, 1RB---_1RC0RC_0RD0RE_1LD1RB_0RB---_------; entry 1, period 8. -/
def p701 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert701 : zipCycle p701 1 8 true (1) = true := by decide +kernel
theorem never701 (m : Machine) (hm : compatible p701 m) : NeverHalts m :=
  zipCycle_sound p701 1 8 true (1) (by decide) cert701 m hm
#print axioms never701


/-- Third-level first-hole refinement 702, 1RB---_1RC0RC_0RD0RE_1LD1RB_1RB---_------; entry 1, period 8. -/
def p702 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert702 : zipCycle p702 1 8 true (1) = true := by decide +kernel
theorem never702 (m : Machine) (hm : compatible p702 m) : NeverHalts m :=
  zipCycle_sound p702 1 8 true (1) (by decide) cert702 m hm
#print axioms never702


/-- Third-level first-hole refinement 703, 1RB---_1RC0RC_0RD0RE_1LD1RB_1LC---_------; entry 1, period 10. -/
def p703 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert703 : zipCycle p703 1 10 true (1) = true := by decide +kernel
theorem never703 (m : Machine) (hm : compatible p703 m) : NeverHalts m :=
  zipCycle_sound p703 1 10 true (1) (by decide) cert703 m hm
#print axioms never703


/-- Third-level first-hole refinement 704, 1RB---_1RC0RC_0RD0RE_1LD1RB_1RC---_------; entry 2, period 7. -/
def p704 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert704 : zipCycle p704 2 7 true (1) = true := by decide +kernel
theorem never704 (m : Machine) (hm : compatible p704 m) : NeverHalts m :=
  zipCycle_sound p704 2 7 true (1) (by decide) cert704 m hm
#print axioms never704


/-- Third-level first-hole refinement 705, 1RB---_1RC0RC_0RD0RE_1LD1RB_0LD---_------; entry 3, period 6. -/
def p705 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert705 : zipCycle p705 3 6 true (1) = true := by decide +kernel
theorem never705 (m : Machine) (hm : compatible p705 m) : NeverHalts m :=
  zipCycle_sound p705 3 6 true (1) (by decide) cert705 m hm
#print axioms never705


/-- Third-level first-hole refinement 706, 1RB---_1RC0RC_0RD0RE_1LD1RB_0RE---_------; entry 8, period 1. -/
def p706 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert706 : zipCycle p706 8 1 true (4) = true := by decide +kernel
theorem never706 (m : Machine) (hm : compatible p706 m) : NeverHalts m :=
  zipCycle_sound p706 8 1 true (4) (by decide) cert706 m hm
#print axioms never706


/-- Third-level first-hole refinement 707, 1RB---_1RC0RC_0RD0RE_1LD1RB_1RE---_------; entry 8, period 1. -/
def p707 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert707 : zipCycle p707 8 1 true (4) = true := by decide +kernel
theorem never707 (m : Machine) (hm : compatible p707 m) : NeverHalts m :=
  zipCycle_sound p707 8 1 true (4) (by decide) cert707 m hm
#print axioms never707


/-- Third-level first-hole refinement 708, 1RB---_1RC0RC_0RD1RE_1LD1RB_0RA---_------; entry 0, period 9. -/
def p708 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert708 : zipCycle p708 0 9 true (0) = true := by decide +kernel
theorem never708 (m : Machine) (hm : compatible p708 m) : NeverHalts m :=
  zipCycle_sound p708 0 9 true (0) (by decide) cert708 m hm
#print axioms never708


/-- Third-level first-hole refinement 709, 1RB---_1RC0RC_0RD1RE_1LD1RB_1RA---_------; entry 0, period 9. -/
def p709 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert709 : zipCycle p709 0 9 true (0) = true := by decide +kernel
theorem never709 (m : Machine) (hm : compatible p709 m) : NeverHalts m :=
  zipCycle_sound p709 0 9 true (0) (by decide) cert709 m hm
#print axioms never709


/-- Third-level first-hole refinement 710, 1RB---_1RC0RC_0RD1RE_1LD1RB_1LB---_------; entry 6, period 3. -/
def p710 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert710 : zipCycle p710 6 3 true (2) = true := by decide +kernel
theorem never710 (m : Machine) (hm : compatible p710 m) : NeverHalts m :=
  zipCycle_sound p710 6 3 true (2) (by decide) cert710 m hm
#print axioms never710


/-- Third-level first-hole refinement 711, 1RB---_1RC0RC_0RD1RE_1LD1RB_0RB---_------; entry 1, period 8. -/
def p711 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert711 : zipCycle p711 1 8 true (1) = true := by decide +kernel
theorem never711 (m : Machine) (hm : compatible p711 m) : NeverHalts m :=
  zipCycle_sound p711 1 8 true (1) (by decide) cert711 m hm
#print axioms never711


/-- Third-level first-hole refinement 712, 1RB---_1RC0RC_0RD1RE_1LD1RB_1RB---_------; entry 1, period 8. -/
def p712 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert712 : zipCycle p712 1 8 true (1) = true := by decide +kernel
theorem never712 (m : Machine) (hm : compatible p712 m) : NeverHalts m :=
  zipCycle_sound p712 1 8 true (1) (by decide) cert712 m hm
#print axioms never712


/-- Third-level first-hole refinement 713, 1RB---_1RC0RC_0RD1RE_1LD1RB_0LC---_------; entry 7, period 2. -/
def p713 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert713 : zipCycle p713 7 2 true (3) = true := by decide +kernel
theorem never713 (m : Machine) (hm : compatible p713 m) : NeverHalts m :=
  zipCycle_sound p713 7 2 true (3) (by decide) cert713 m hm
#print axioms never713


/-- Third-level first-hole refinement 714, 1RB---_1RC0RC_0RD1RE_1LD1RB_1RC---_------; entry 2, period 7. -/
def p714 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert714 : zipCycle p714 2 7 true (1) = true := by decide +kernel
theorem never714 (m : Machine) (hm : compatible p714 m) : NeverHalts m :=
  zipCycle_sound p714 2 7 true (1) (by decide) cert714 m hm
#print axioms never714


/-- Third-level first-hole refinement 715, 1RB---_1RC0RC_0RD1RE_1LD1RB_0LD---_------; entry 1, period 9. -/
def p715 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert715 : zipCycle p715 1 9 true (1) = true := by decide +kernel
theorem never715 (m : Machine) (hm : compatible p715 m) : NeverHalts m :=
  zipCycle_sound p715 1 9 true (1) (by decide) cert715 m hm
#print axioms never715


/-- Third-level first-hole refinement 716, 1RB---_1RC0RC_0RD1RE_1LD1RB_0RD---_------; entry 3, period 6. -/
def p716 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert716 : zipCycle p716 3 6 true (1) = true := by decide +kernel
theorem never716 (m : Machine) (hm : compatible p716 m) : NeverHalts m :=
  zipCycle_sound p716 3 6 true (1) (by decide) cert716 m hm
#print axioms never716


/-- Third-level first-hole refinement 717, 1RB---_1RC0RC_0RD1RE_1LD1RB_0RE---_------; entry 8, period 1. -/
def p717 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert717 : zipCycle p717 8 1 true (4) = true := by decide +kernel
theorem never717 (m : Machine) (hm : compatible p717 m) : NeverHalts m :=
  zipCycle_sound p717 8 1 true (4) (by decide) cert717 m hm
#print axioms never717


/-- Third-level first-hole refinement 718, 1RB---_1RC0RC_0RD1RE_1LD1RB_1RE---_------; entry 8, period 1. -/
def p718 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert718 : zipCycle p718 8 1 true (4) = true := by decide +kernel
theorem never718 (m : Machine) (hm : compatible p718 m) : NeverHalts m :=
  zipCycle_sound p718 8 1 true (4) (by decide) cert718 m hm
#print axioms never718


/-- Third-level first-hole refinement 719, 1RB0LA_1RC1RC_0RD0LA_1LD1RB_------_------; entry 0, period 11. -/
def p719 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert719 : zipCycle p719 0 11 false (3) = true := by decide +kernel
theorem never719 (m : Machine) (hm : compatible p719 m) : NeverHalts m :=
  zipCycle_sound p719 0 11 false (3) (by decide) cert719 m hm
#print axioms never719


/-- Third-level first-hole refinement 720, 1RB1LA_1RC1RC_0RD0LA_1LD1RB_------_------; entry 9, period 5. -/
def p720 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert720 : zipCycle p720 9 5 false (1) = true := by decide +kernel
theorem never720 (m : Machine) (hm : compatible p720 m) : NeverHalts m :=
  zipCycle_sound p720 9 5 false (1) (by decide) cert720 m hm
#print axioms never720


/-- Third-level first-hole refinement 721, 1RB0RA_1RC1RC_0RD0LA_1LD1RB_------_------; entry 0, period 9. -/
def p721 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert721 : zipCycle p721 0 9 true (0) = true := by decide +kernel
theorem never721 (m : Machine) (hm : compatible p721 m) : NeverHalts m :=
  zipCycle_sound p721 0 9 true (0) (by decide) cert721 m hm
#print axioms never721


/-- Third-level first-hole refinement 722, 1RB1RA_1RC1RC_0RD0LA_1LD1RB_------_------; entry 0, period 9. -/
def p722 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert722 : zipCycle p722 0 9 true (0) = true := by decide +kernel
theorem never722 (m : Machine) (hm : compatible p722 m) : NeverHalts m :=
  zipCycle_sound p722 0 9 true (0) (by decide) cert722 m hm
#print axioms never722


/-- Third-level first-hole refinement 723, 1RB0LB_1RC1RC_0RD0LA_1LD1RB_------_------; entry 2, period 8. -/
def p723 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert723 : zipCycle p723 2 8 true (1) = true := by decide +kernel
theorem never723 (m : Machine) (hm : compatible p723 m) : NeverHalts m :=
  zipCycle_sound p723 2 8 true (1) (by decide) cert723 m hm
#print axioms never723


/-- Third-level first-hole refinement 724, 1RB1LB_1RC1RC_0RD0LA_1LD1RB_------_------; entry 13, period 3. -/
def p724 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert724 : zipCycle p724 13 3 false (1) = true := by decide +kernel
theorem never724 (m : Machine) (hm : compatible p724 m) : NeverHalts m :=
  zipCycle_sound p724 13 3 false (1) (by decide) cert724 m hm
#print axioms never724


/-- Third-level first-hole refinement 725, 1RB0RB_1RC1RC_0RD0LA_1LD1RB_------_------; entry 1, period 8. -/
def p725 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert725 : zipCycle p725 1 8 true (1) = true := by decide +kernel
theorem never725 (m : Machine) (hm : compatible p725 m) : NeverHalts m :=
  zipCycle_sound p725 1 8 true (1) (by decide) cert725 m hm
#print axioms never725


/-- Third-level first-hole refinement 726, 1RB1RB_1RC1RC_0RD0LA_1LD1RB_------_------; entry 1, period 8. -/
def p726 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert726 : zipCycle p726 1 8 true (1) = true := by decide +kernel
theorem never726 (m : Machine) (hm : compatible p726 m) : NeverHalts m :=
  zipCycle_sound p726 1 8 true (1) (by decide) cert726 m hm
#print axioms never726


/-- Third-level first-hole refinement 727, 1RB0LC_1RC1RC_0RD0LA_1LD1RB_------_------; entry 12, period 1. -/
def p727 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert727 : zipCycle p727 12 1 false (0) = true := by decide +kernel
theorem never727 (m : Machine) (hm : compatible p727 m) : NeverHalts m :=
  zipCycle_sound p727 12 1 false (0) (by decide) cert727 m hm
#print axioms never727


/-- Third-level first-hole refinement 728, 1RB1LC_1RC1RC_0RD0LA_1LD1RB_------_------; entry 13, period 5. -/
def p728 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert728 : zipCycle p728 13 5 false (2) = true := by decide +kernel
theorem never728 (m : Machine) (hm : compatible p728 m) : NeverHalts m :=
  zipCycle_sound p728 13 5 false (2) (by decide) cert728 m hm
#print axioms never728


/-- Third-level first-hole refinement 729, 1RB0RC_1RC1RC_0RD0LA_1LD1RB_------_------; entry 1, period 18. -/
def p729 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert729 : zipCycle p729 1 18 true (1) = true := by decide +kernel
theorem never729 (m : Machine) (hm : compatible p729 m) : NeverHalts m :=
  zipCycle_sound p729 1 18 true (1) (by decide) cert729 m hm
#print axioms never729


/-- Third-level first-hole refinement 730, 1RB1RC_1RC1RC_0RD0LA_1LD1RB_------_------; entry 2, period 7. -/
def p730 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert730 : zipCycle p730 2 7 true (1) = true := by decide +kernel
theorem never730 (m : Machine) (hm : compatible p730 m) : NeverHalts m :=
  zipCycle_sound p730 2 7 true (1) (by decide) cert730 m hm
#print axioms never730


/-- Third-level first-hole refinement 731, 1RB0LD_1RC1RC_0RD0LA_1LD1RB_------_------; entry 1, period 9. -/
def p731 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert731 : zipCycle p731 1 9 true (1) = true := by decide +kernel
theorem never731 (m : Machine) (hm : compatible p731 m) : NeverHalts m :=
  zipCycle_sound p731 1 9 true (1) (by decide) cert731 m hm
#print axioms never731


/-- Third-level first-hole refinement 732, 1RB1LD_1RC1RC_0RD0LA_1LD1RB_------_------; entry 2, period 9. -/
def p732 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert732 : zipCycle p732 2 9 true (1) = true := by decide +kernel
theorem never732 (m : Machine) (hm : compatible p732 m) : NeverHalts m :=
  zipCycle_sound p732 2 9 true (1) (by decide) cert732 m hm
#print axioms never732


/-- Third-level first-hole refinement 733, 1RB0RD_1RC1RC_0RD0LA_1LD1RB_------_------; entry 3, period 6. -/
def p733 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert733 : zipCycle p733 3 6 true (1) = true := by decide +kernel
theorem never733 (m : Machine) (hm : compatible p733 m) : NeverHalts m :=
  zipCycle_sound p733 3 6 true (1) (by decide) cert733 m hm
#print axioms never733


/-- Third-level first-hole refinement 734, 1RB1RD_1RC1RC_0RD0LA_1LD1RB_------_------; entry 2, period 10. -/
def p734 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert734 : zipCycle p734 2 10 true (1) = true := by decide +kernel
theorem never734 (m : Machine) (hm : compatible p734 m) : NeverHalts m :=
  zipCycle_sound p734 2 10 true (1) (by decide) cert734 m hm
#print axioms never734


/-- Third-level first-hole refinement 735, 1RB0LA_1RC1RC_0RD1LA_1LD1RB_------_------; entry 0, period 11. -/
def p735 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert735 : zipCycle p735 0 11 false (3) = true := by decide +kernel
theorem never735 (m : Machine) (hm : compatible p735 m) : NeverHalts m :=
  zipCycle_sound p735 0 11 false (3) (by decide) cert735 m hm
#print axioms never735


/-- Third-level first-hole refinement 736, 1RB1LA_1RC1RC_0RD1LA_1LD1RB_------_------; entry 9, period 5. -/
def p736 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert736 : zipCycle p736 9 5 false (1) = true := by decide +kernel
theorem never736 (m : Machine) (hm : compatible p736 m) : NeverHalts m :=
  zipCycle_sound p736 9 5 false (1) (by decide) cert736 m hm
#print axioms never736


/-- Third-level first-hole refinement 737, 1RB0RA_1RC1RC_0RD1LA_1LD1RB_------_------; entry 0, period 10. -/
def p737 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert737 : zipCycle p737 0 10 true (0) = true := by decide +kernel
theorem never737 (m : Machine) (hm : compatible p737 m) : NeverHalts m :=
  zipCycle_sound p737 0 10 true (0) (by decide) cert737 m hm
#print axioms never737


/-- Third-level first-hole refinement 738, 1RB1RA_1RC1RC_0RD1LA_1LD1RB_------_------; entry 0, period 10. -/
def p738 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert738 : zipCycle p738 0 10 true (0) = true := by decide +kernel
theorem never738 (m : Machine) (hm : compatible p738 m) : NeverHalts m :=
  zipCycle_sound p738 0 10 true (0) (by decide) cert738 m hm
#print axioms never738


/-- Third-level first-hole refinement 739, 1RB0LB_1RC1RC_0RD1LA_1LD1RB_------_------; entry 1, period 11. -/
def p739 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert739 : zipCycle p739 1 11 true (1) = true := by decide +kernel
theorem never739 (m : Machine) (hm : compatible p739 m) : NeverHalts m :=
  zipCycle_sound p739 1 11 true (1) (by decide) cert739 m hm
#print axioms never739


/-- Third-level first-hole refinement 740, 1RB1LB_1RC1RC_0RD1LA_1LD1RB_------_------; entry 13, period 3. -/
def p740 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert740 : zipCycle p740 13 3 false (1) = true := by decide +kernel
theorem never740 (m : Machine) (hm : compatible p740 m) : NeverHalts m :=
  zipCycle_sound p740 13 3 false (1) (by decide) cert740 m hm
#print axioms never740


/-- Third-level first-hole refinement 741, 1RB0RB_1RC1RC_0RD1LA_1LD1RB_------_------; entry 2, period 8. -/
def p741 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert741 : zipCycle p741 2 8 true (1) = true := by decide +kernel
theorem never741 (m : Machine) (hm : compatible p741 m) : NeverHalts m :=
  zipCycle_sound p741 2 8 true (1) (by decide) cert741 m hm
#print axioms never741


/-- Third-level first-hole refinement 742, 1RB1RB_1RC1RC_0RD1LA_1LD1RB_------_------; entry 2, period 8. -/
def p742 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert742 : zipCycle p742 2 8 true (1) = true := by decide +kernel
theorem never742 (m : Machine) (hm : compatible p742 m) : NeverHalts m :=
  zipCycle_sound p742 2 8 true (1) (by decide) cert742 m hm
#print axioms never742


/-- Third-level first-hole refinement 743, 1RB0LC_1RC1RC_0RD1LA_1LD1RB_------_------; entry 12, period 1. -/
def p743 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert743 : zipCycle p743 12 1 false (0) = true := by decide +kernel
theorem never743 (m : Machine) (hm : compatible p743 m) : NeverHalts m :=
  zipCycle_sound p743 12 1 false (0) (by decide) cert743 m hm
#print axioms never743


/-- Third-level first-hole refinement 744, 1RB1LC_1RC1RC_0RD1LA_1LD1RB_------_------; entry 13, period 5. -/
def p744 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert744 : zipCycle p744 13 5 false (2) = true := by decide +kernel
theorem never744 (m : Machine) (hm : compatible p744 m) : NeverHalts m :=
  zipCycle_sound p744 13 5 false (2) (by decide) cert744 m hm
#print axioms never744


/-- Third-level first-hole refinement 745, 1RB0RC_1RC1RC_0RD1LA_1LD1RB_------_------; entry 2, period 10. -/
def p745 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert745 : zipCycle p745 2 10 true (1) = true := by decide +kernel
theorem never745 (m : Machine) (hm : compatible p745 m) : NeverHalts m :=
  zipCycle_sound p745 2 10 true (1) (by decide) cert745 m hm
#print axioms never745


/-- Third-level first-hole refinement 746, 1RB1RC_1RC1RC_0RD1LA_1LD1RB_------_------; entry 7, period 2. -/
def p746 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert746 : zipCycle p746 7 2 true (2) = true := by decide +kernel
theorem never746 (m : Machine) (hm : compatible p746 m) : NeverHalts m :=
  zipCycle_sound p746 7 2 true (2) (by decide) cert746 m hm
#print axioms never746


/-- Third-level first-hole refinement 747, 1RB0LD_1RC1RC_0RD1LA_1LD1RB_------_------; entry 7, period 4. -/
def p747 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert747 : zipCycle p747 7 4 true (1) = true := by decide +kernel
theorem never747 (m : Machine) (hm : compatible p747 m) : NeverHalts m :=
  zipCycle_sound p747 7 4 true (1) (by decide) cert747 m hm
#print axioms never747


/-- Third-level first-hole refinement 748, 1RB1LD_1RC1RC_0RD1LA_1LD1RB_------_------; entry 5, period 4. -/
def p748 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert748 : zipCycle p748 5 4 true (1) = true := by decide +kernel
theorem never748 (m : Machine) (hm : compatible p748 m) : NeverHalts m :=
  zipCycle_sound p748 5 4 true (1) (by decide) cert748 m hm
#print axioms never748


/-- Third-level first-hole refinement 749, 1RB0RD_1RC1RC_0RD1LA_1LD1RB_------_------; entry 1, period 9. -/
def p749 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert749 : zipCycle p749 1 9 true (1) = true := by decide +kernel
theorem never749 (m : Machine) (hm : compatible p749 m) : NeverHalts m :=
  zipCycle_sound p749 1 9 true (1) (by decide) cert749 m hm
#print axioms never749


/-- Third-level first-hole refinement 750, 1RB1RD_1RC1RC_0RD1LA_1LD1RB_------_------; entry 1, period 9. -/
def p750 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert750 : zipCycle p750 1 9 true (1) = true := by decide +kernel
theorem never750 (m : Machine) (hm : compatible p750 m) : NeverHalts m :=
  zipCycle_sound p750 1 9 true (1) (by decide) cert750 m hm
#print axioms never750


/-- Third-level first-hole refinement 751, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0RA_------; entry 0, period 9. -/
def p751 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert751 : zipCycle p751 0 9 true (0) = true := by decide +kernel
theorem never751 (m : Machine) (hm : compatible p751 m) : NeverHalts m :=
  zipCycle_sound p751 0 9 true (0) (by decide) cert751 m hm
#print axioms never751


/-- Third-level first-hole refinement 752, 1RB---_1RC1RC_0RD0LE_1LD1RB_---1RA_------; entry 0, period 9. -/
def p752 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert752 : zipCycle p752 0 9 true (0) = true := by decide +kernel
theorem never752 (m : Machine) (hm : compatible p752 m) : NeverHalts m :=
  zipCycle_sound p752 0 9 true (0) (by decide) cert752 m hm
#print axioms never752


/-- Third-level first-hole refinement 753, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0LB_------; entry 2, period 8. -/
def p753 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert753 : zipCycle p753 2 8 true (1) = true := by decide +kernel
theorem never753 (m : Machine) (hm : compatible p753 m) : NeverHalts m :=
  zipCycle_sound p753 2 8 true (1) (by decide) cert753 m hm
#print axioms never753


/-- Third-level first-hole refinement 754, 1RB---_1RC1RC_0RD0LE_1LD1RB_---1LB_------; entry 13, period 3. -/
def p754 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert754 : zipCycle p754 13 3 false (1) = true := by decide +kernel
theorem never754 (m : Machine) (hm : compatible p754 m) : NeverHalts m :=
  zipCycle_sound p754 13 3 false (1) (by decide) cert754 m hm
#print axioms never754


/-- Third-level first-hole refinement 755, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0RB_------; entry 1, period 8. -/
def p755 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert755 : zipCycle p755 1 8 true (1) = true := by decide +kernel
theorem never755 (m : Machine) (hm : compatible p755 m) : NeverHalts m :=
  zipCycle_sound p755 1 8 true (1) (by decide) cert755 m hm
#print axioms never755


/-- Third-level first-hole refinement 756, 1RB---_1RC1RC_0RD0LE_1LD1RB_---1RB_------; entry 1, period 8. -/
def p756 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert756 : zipCycle p756 1 8 true (1) = true := by decide +kernel
theorem never756 (m : Machine) (hm : compatible p756 m) : NeverHalts m :=
  zipCycle_sound p756 1 8 true (1) (by decide) cert756 m hm
#print axioms never756


/-- Third-level first-hole refinement 757, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0LC_------; entry 12, period 1. -/
def p757 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert757 : zipCycle p757 12 1 false (0) = true := by decide +kernel
theorem never757 (m : Machine) (hm : compatible p757 m) : NeverHalts m :=
  zipCycle_sound p757 12 1 false (0) (by decide) cert757 m hm
#print axioms never757


/-- Third-level first-hole refinement 758, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0RC_------; entry 1, period 18. -/
def p758 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert758 : zipCycle p758 1 18 true (1) = true := by decide +kernel
theorem never758 (m : Machine) (hm : compatible p758 m) : NeverHalts m :=
  zipCycle_sound p758 1 18 true (1) (by decide) cert758 m hm
#print axioms never758


/-- Third-level first-hole refinement 759, 1RB---_1RC1RC_0RD0LE_1LD1RB_---1RC_------; entry 2, period 7. -/
def p759 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert759 : zipCycle p759 2 7 true (1) = true := by decide +kernel
theorem never759 (m : Machine) (hm : compatible p759 m) : NeverHalts m :=
  zipCycle_sound p759 2 7 true (1) (by decide) cert759 m hm
#print axioms never759


/-- Third-level first-hole refinement 760, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0LD_------; entry 1, period 9. -/
def p760 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert760 : zipCycle p760 1 9 true (1) = true := by decide +kernel
theorem never760 (m : Machine) (hm : compatible p760 m) : NeverHalts m :=
  zipCycle_sound p760 1 9 true (1) (by decide) cert760 m hm
#print axioms never760


/-- Third-level first-hole refinement 761, 1RB---_1RC1RC_0RD0LE_1LD1RB_---1LD_------; entry 2, period 9. -/
def p761 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert761 : zipCycle p761 2 9 true (1) = true := by decide +kernel
theorem never761 (m : Machine) (hm : compatible p761 m) : NeverHalts m :=
  zipCycle_sound p761 2 9 true (1) (by decide) cert761 m hm
#print axioms never761


/-- Third-level first-hole refinement 762, 1RB---_1RC1RC_0RD0LE_1LD1RB_---0RD_------; entry 3, period 6. -/
def p762 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert762 : zipCycle p762 3 6 true (1) = true := by decide +kernel
theorem never762 (m : Machine) (hm : compatible p762 m) : NeverHalts m :=
  zipCycle_sound p762 3 6 true (1) (by decide) cert762 m hm
#print axioms never762


/-- Third-level first-hole refinement 763, 1RB---_1RC1RC_0RD0LE_1LD1RB_---1RD_------; entry 2, period 10. -/
def p763 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert763 : zipCycle p763 2 10 true (1) = true := by decide +kernel
theorem never763 (m : Machine) (hm : compatible p763 m) : NeverHalts m :=
  zipCycle_sound p763 2 10 true (1) (by decide) cert763 m hm
#print axioms never763


/-- Third-level first-hole refinement 764, 1RB---_1RC1RC_0RD1LE_1LD1RB_---0LB_------; entry 1, period 11. -/
def p764 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert764 : zipCycle p764 1 11 true (1) = true := by decide +kernel
theorem never764 (m : Machine) (hm : compatible p764 m) : NeverHalts m :=
  zipCycle_sound p764 1 11 true (1) (by decide) cert764 m hm
#print axioms never764


/-- Third-level first-hole refinement 765, 1RB---_1RC1RC_0RD1LE_1LD1RB_---1LB_------; entry 13, period 3. -/
def p765 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert765 : zipCycle p765 13 3 false (1) = true := by decide +kernel
theorem never765 (m : Machine) (hm : compatible p765 m) : NeverHalts m :=
  zipCycle_sound p765 13 3 false (1) (by decide) cert765 m hm
#print axioms never765


/-- Third-level first-hole refinement 766, 1RB---_1RC1RC_0RD1LE_1LD1RB_---0RB_------; entry 2, period 8. -/
def p766 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert766 : zipCycle p766 2 8 true (1) = true := by decide +kernel
theorem never766 (m : Machine) (hm : compatible p766 m) : NeverHalts m :=
  zipCycle_sound p766 2 8 true (1) (by decide) cert766 m hm
#print axioms never766


/-- Third-level first-hole refinement 767, 1RB---_1RC1RC_0RD1LE_1LD1RB_---1RB_------; entry 2, period 8. -/
def p767 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert767 : zipCycle p767 2 8 true (1) = true := by decide +kernel
theorem never767 (m : Machine) (hm : compatible p767 m) : NeverHalts m :=
  zipCycle_sound p767 2 8 true (1) (by decide) cert767 m hm
#print axioms never767


/-- Third-level first-hole refinement 768, 1RB---_1RC1RC_0RD1LE_1LD1RB_---0LC_------; entry 12, period 1. -/
def p768 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert768 : zipCycle p768 12 1 false (0) = true := by decide +kernel
theorem never768 (m : Machine) (hm : compatible p768 m) : NeverHalts m :=
  zipCycle_sound p768 12 1 false (0) (by decide) cert768 m hm
#print axioms never768


/-- Third-level first-hole refinement 769, 1RB---_1RC1RC_0RD1LE_1LD1RB_---1RC_------; entry 7, period 2. -/
def p769 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert769 : zipCycle p769 7 2 true (2) = true := by decide +kernel
theorem never769 (m : Machine) (hm : compatible p769 m) : NeverHalts m :=
  zipCycle_sound p769 7 2 true (2) (by decide) cert769 m hm
#print axioms never769


/-- Third-level first-hole refinement 770, 1RB---_1RC1RC_0RD1LE_1LD1RB_---0LD_------; entry 7, period 4. -/
def p770 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert770 : zipCycle p770 7 4 true (1) = true := by decide +kernel
theorem never770 (m : Machine) (hm : compatible p770 m) : NeverHalts m :=
  zipCycle_sound p770 7 4 true (1) (by decide) cert770 m hm
#print axioms never770


/-- Third-level first-hole refinement 771, 1RB---_1RC1RC_0RD1LE_1LD1RB_---1LD_------; entry 5, period 4. -/
def p771 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert771 : zipCycle p771 5 4 true (1) = true := by decide +kernel
theorem never771 (m : Machine) (hm : compatible p771 m) : NeverHalts m :=
  zipCycle_sound p771 5 4 true (1) (by decide) cert771 m hm
#print axioms never771


/-- Third-level first-hole refinement 772, 1RB---_1RC1RC_0RD1LE_1LD1RB_---0RD_------; entry 1, period 9. -/
def p772 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert772 : zipCycle p772 1 9 true (1) = true := by decide +kernel
theorem never772 (m : Machine) (hm : compatible p772 m) : NeverHalts m :=
  zipCycle_sound p772 1 9 true (1) (by decide) cert772 m hm
#print axioms never772


/-- Third-level first-hole refinement 773, 1RB---_1RC1RC_0RD1LE_1LD1RB_---1RD_------; entry 1, period 9. -/
def p773 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert773 : zipCycle p773 1 9 true (1) = true := by decide +kernel
theorem never773 (m : Machine) (hm : compatible p773 m) : NeverHalts m :=
  zipCycle_sound p773 1 9 true (1) (by decide) cert773 m hm
#print axioms never773


/-- Third-level first-hole refinement 774, 1RB---_1RC1RC_0RD0RE_1LD1RB_0LA---_------; entry 0, period 9. -/
def p774 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert774 : zipCycle p774 0 9 true (0) = true := by decide +kernel
theorem never774 (m : Machine) (hm : compatible p774 m) : NeverHalts m :=
  zipCycle_sound p774 0 9 true (0) (by decide) cert774 m hm
#print axioms never774


/-- Third-level first-hole refinement 775, 1RB---_1RC1RC_0RD0RE_1LD1RB_1LA---_------; entry 2, period 9. -/
def p775 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert775 : zipCycle p775 2 9 true (1) = true := by decide +kernel
theorem never775 (m : Machine) (hm : compatible p775 m) : NeverHalts m :=
  zipCycle_sound p775 2 9 true (1) (by decide) cert775 m hm
#print axioms never775


/-- Third-level first-hole refinement 776, 1RB---_1RC1RC_0RD0RE_1LD1RB_0RA---_------; entry 0, period 9. -/
def p776 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert776 : zipCycle p776 0 9 true (0) = true := by decide +kernel
theorem never776 (m : Machine) (hm : compatible p776 m) : NeverHalts m :=
  zipCycle_sound p776 0 9 true (0) (by decide) cert776 m hm
#print axioms never776


/-- Third-level first-hole refinement 777, 1RB---_1RC1RC_0RD0RE_1LD1RB_1RA---_------; entry 0, period 9. -/
def p777 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert777 : zipCycle p777 0 9 true (0) = true := by decide +kernel
theorem never777 (m : Machine) (hm : compatible p777 m) : NeverHalts m :=
  zipCycle_sound p777 0 9 true (0) (by decide) cert777 m hm
#print axioms never777


/-- Third-level first-hole refinement 778, 1RB---_1RC1RC_0RD0RE_1LD1RB_0LB---_------; entry 1, period 8. -/
def p778 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert778 : zipCycle p778 1 8 true (1) = true := by decide +kernel
theorem never778 (m : Machine) (hm : compatible p778 m) : NeverHalts m :=
  zipCycle_sound p778 1 8 true (1) (by decide) cert778 m hm
#print axioms never778


/-- Third-level first-hole refinement 779, 1RB---_1RC1RC_0RD0RE_1LD1RB_1LB---_------; entry 7, period 3. -/
def p779 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert779 : zipCycle p779 7 3 true (3) = true := by decide +kernel
theorem never779 (m : Machine) (hm : compatible p779 m) : NeverHalts m :=
  zipCycle_sound p779 7 3 true (3) (by decide) cert779 m hm
#print axioms never779


/-- Third-level first-hole refinement 780, 1RB---_1RC1RC_0RD0RE_1LD1RB_0RB---_------; entry 1, period 8. -/
def p780 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert780 : zipCycle p780 1 8 true (1) = true := by decide +kernel
theorem never780 (m : Machine) (hm : compatible p780 m) : NeverHalts m :=
  zipCycle_sound p780 1 8 true (1) (by decide) cert780 m hm
#print axioms never780


/-- Third-level first-hole refinement 781, 1RB---_1RC1RC_0RD0RE_1LD1RB_1RB---_------; entry 1, period 8. -/
def p781 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert781 : zipCycle p781 1 8 true (1) = true := by decide +kernel
theorem never781 (m : Machine) (hm : compatible p781 m) : NeverHalts m :=
  zipCycle_sound p781 1 8 true (1) (by decide) cert781 m hm
#print axioms never781


/-- Third-level first-hole refinement 782, 1RB---_1RC1RC_0RD0RE_1LD1RB_0LC---_------; entry 2, period 7. -/
def p782 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert782 : zipCycle p782 2 7 true (1) = true := by decide +kernel
theorem never782 (m : Machine) (hm : compatible p782 m) : NeverHalts m :=
  zipCycle_sound p782 2 7 true (1) (by decide) cert782 m hm
#print axioms never782


/-- Third-level first-hole refinement 783, 1RB---_1RC1RC_0RD0RE_1LD1RB_1LC---_------; entry 1, period 10. -/
def p783 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert783 : zipCycle p783 1 10 true (1) = true := by decide +kernel
theorem never783 (m : Machine) (hm : compatible p783 m) : NeverHalts m :=
  zipCycle_sound p783 1 10 true (1) (by decide) cert783 m hm
#print axioms never783


/-- Third-level first-hole refinement 784, 1RB---_1RC1RC_0RD0RE_1LD1RB_1RC---_------; entry 2, period 7. -/
def p784 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert784 : zipCycle p784 2 7 true (1) = true := by decide +kernel
theorem never784 (m : Machine) (hm : compatible p784 m) : NeverHalts m :=
  zipCycle_sound p784 2 7 true (1) (by decide) cert784 m hm
#print axioms never784


/-- Third-level first-hole refinement 785, 1RB---_1RC1RC_0RD0RE_1LD1RB_0LD---_------; entry 2, period 10. -/
def p785 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert785 : zipCycle p785 2 10 true (1) = true := by decide +kernel
theorem never785 (m : Machine) (hm : compatible p785 m) : NeverHalts m :=
  zipCycle_sound p785 2 10 true (1) (by decide) cert785 m hm
#print axioms never785


/-- Third-level first-hole refinement 786, 1RB---_1RC1RC_0RD0RE_1LD1RB_1LD---_------; entry 4, period 5. -/
def p786 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert786 : zipCycle p786 4 5 true (1) = true := by decide +kernel
theorem never786 (m : Machine) (hm : compatible p786 m) : NeverHalts m :=
  zipCycle_sound p786 4 5 true (1) (by decide) cert786 m hm
#print axioms never786


/-- Third-level first-hole refinement 787, 1RB---_1RC1RC_0RD0RE_1LD1RB_1RD---_------; entry 2, period 10. -/
def p787 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert787 : zipCycle p787 2 10 true (1) = true := by decide +kernel
theorem never787 (m : Machine) (hm : compatible p787 m) : NeverHalts m :=
  zipCycle_sound p787 2 10 true (1) (by decide) cert787 m hm
#print axioms never787


/-- Third-level first-hole refinement 788, 1RB---_1RC1RC_0RD0RE_1LD1RB_0RE---_------; entry 8, period 1. -/
def p788 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert788 : zipCycle p788 8 1 true (4) = true := by decide +kernel
theorem never788 (m : Machine) (hm : compatible p788 m) : NeverHalts m :=
  zipCycle_sound p788 8 1 true (4) (by decide) cert788 m hm
#print axioms never788


/-- Third-level first-hole refinement 789, 1RB---_1RC1RC_0RD0RE_1LD1RB_1RE---_------; entry 8, period 1. -/
def p789 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert789 : zipCycle p789 8 1 true (4) = true := by decide +kernel
theorem never789 (m : Machine) (hm : compatible p789 m) : NeverHalts m :=
  zipCycle_sound p789 8 1 true (4) (by decide) cert789 m hm
#print axioms never789


/-- Third-level first-hole refinement 790, 1RB---_1RC1RC_0RD1RE_1LD1RB_0RA---_------; entry 0, period 9. -/
def p790 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert790 : zipCycle p790 0 9 true (0) = true := by decide +kernel
theorem never790 (m : Machine) (hm : compatible p790 m) : NeverHalts m :=
  zipCycle_sound p790 0 9 true (0) (by decide) cert790 m hm
#print axioms never790


/-- Third-level first-hole refinement 791, 1RB---_1RC1RC_0RD1RE_1LD1RB_1RA---_------; entry 0, period 9. -/
def p791 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert791 : zipCycle p791 0 9 true (0) = true := by decide +kernel
theorem never791 (m : Machine) (hm : compatible p791 m) : NeverHalts m :=
  zipCycle_sound p791 0 9 true (0) (by decide) cert791 m hm
#print axioms never791


/-- Third-level first-hole refinement 792, 1RB---_1RC1RC_0RD1RE_1LD1RB_0LB---_------; entry 2, period 8. -/
def p792 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert792 : zipCycle p792 2 8 true (1) = true := by decide +kernel
theorem never792 (m : Machine) (hm : compatible p792 m) : NeverHalts m :=
  zipCycle_sound p792 2 8 true (1) (by decide) cert792 m hm
#print axioms never792


/-- Third-level first-hole refinement 793, 1RB---_1RC1RC_0RD1RE_1LD1RB_1LB---_------; entry 6, period 3. -/
def p793 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert793 : zipCycle p793 6 3 true (2) = true := by decide +kernel
theorem never793 (m : Machine) (hm : compatible p793 m) : NeverHalts m :=
  zipCycle_sound p793 6 3 true (2) (by decide) cert793 m hm
#print axioms never793


/-- Third-level first-hole refinement 794, 1RB---_1RC1RC_0RD1RE_1LD1RB_0RB---_------; entry 1, period 8. -/
def p794 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert794 : zipCycle p794 1 8 true (1) = true := by decide +kernel
theorem never794 (m : Machine) (hm : compatible p794 m) : NeverHalts m :=
  zipCycle_sound p794 1 8 true (1) (by decide) cert794 m hm
#print axioms never794


/-- Third-level first-hole refinement 795, 1RB---_1RC1RC_0RD1RE_1LD1RB_1RB---_------; entry 1, period 8. -/
def p795 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert795 : zipCycle p795 1 8 true (1) = true := by decide +kernel
theorem never795 (m : Machine) (hm : compatible p795 m) : NeverHalts m :=
  zipCycle_sound p795 1 8 true (1) (by decide) cert795 m hm
#print axioms never795


/-- Third-level first-hole refinement 796, 1RB---_1RC1RC_0RD1RE_1LD1RB_0LC---_------; entry 7, period 2. -/
def p796 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert796 : zipCycle p796 7 2 true (3) = true := by decide +kernel
theorem never796 (m : Machine) (hm : compatible p796 m) : NeverHalts m :=
  zipCycle_sound p796 7 2 true (3) (by decide) cert796 m hm
#print axioms never796


/-- Third-level first-hole refinement 797, 1RB---_1RC1RC_0RD1RE_1LD1RB_1RC---_------; entry 2, period 7. -/
def p797 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert797 : zipCycle p797 2 7 true (1) = true := by decide +kernel
theorem never797 (m : Machine) (hm : compatible p797 m) : NeverHalts m :=
  zipCycle_sound p797 2 7 true (1) (by decide) cert797 m hm
#print axioms never797


/-- Third-level first-hole refinement 798, 1RB---_1RC1RC_0RD1RE_1LD1RB_0LD---_------; entry 1, period 9. -/
def p798 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert798 : zipCycle p798 1 9 true (1) = true := by decide +kernel
theorem never798 (m : Machine) (hm : compatible p798 m) : NeverHalts m :=
  zipCycle_sound p798 1 9 true (1) (by decide) cert798 m hm
#print axioms never798


/-- Third-level first-hole refinement 799, 1RB---_1RC1RC_0RD1RE_1LD1RB_1LD---_------; entry 2, period 9. -/
def p799 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert799 : zipCycle p799 2 9 true (1) = true := by decide +kernel
theorem never799 (m : Machine) (hm : compatible p799 m) : NeverHalts m :=
  zipCycle_sound p799 2 9 true (1) (by decide) cert799 m hm
#print axioms never799

end BB6.Agent24Raw45D3_07
