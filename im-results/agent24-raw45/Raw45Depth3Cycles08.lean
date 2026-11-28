import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_08
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 800, 1RB---_1RC1RC_0RD1RE_1LD1RB_0RD---_------; entry 3, period 6. -/
def p800 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert800 : zipCycle p800 3 6 true (1) = true := by decide +kernel
theorem never800 (m : Machine) (hm : compatible p800 m) : NeverHalts m :=
  zipCycle_sound p800 3 6 true (1) (by decide) cert800 m hm
#print axioms never800


/-- Third-level first-hole refinement 801, 1RB---_1RC1RC_0RD1RE_1LD1RB_1RD---_------; entry 2, period 10. -/
def p801 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert801 : zipCycle p801 2 10 true (1) = true := by decide +kernel
theorem never801 (m : Machine) (hm : compatible p801 m) : NeverHalts m :=
  zipCycle_sound p801 2 10 true (1) (by decide) cert801 m hm
#print axioms never801


/-- Third-level first-hole refinement 802, 1RB---_1RC1RC_0RD1RE_1LD1RB_0RE---_------; entry 8, period 1. -/
def p802 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert802 : zipCycle p802 8 1 true (4) = true := by decide +kernel
theorem never802 (m : Machine) (hm : compatible p802 m) : NeverHalts m :=
  zipCycle_sound p802 8 1 true (4) (by decide) cert802 m hm
#print axioms never802


/-- Third-level first-hole refinement 803, 1RB---_1RC1RC_0RD1RE_1LD1RB_1RE---_------; entry 8, period 1. -/
def p803 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨true,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert803 : zipCycle p803 8 1 true (4) = true := by decide +kernel
theorem never803 (m : Machine) (hm : compatible p803 m) : NeverHalts m :=
  zipCycle_sound p803 8 1 true (4) (by decide) cert803 m hm
#print axioms never803


/-- Third-level first-hole refinement 804, 1RB0LA_1RC0LD_0RD0LA_1LD1RB_------_------; entry 0, period 13. -/
def p804 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert804 : zipCycle p804 0 13 false (3) = true := by decide +kernel
theorem never804 (m : Machine) (hm : compatible p804 m) : NeverHalts m :=
  zipCycle_sound p804 0 13 false (3) (by decide) cert804 m hm
#print axioms never804


/-- Third-level first-hole refinement 805, 1RB1LA_1RC0LD_0RD0LA_1LD1RB_------_------; entry 11, period 7. -/
def p805 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert805 : zipCycle p805 11 7 false (1) = true := by decide +kernel
theorem never805 (m : Machine) (hm : compatible p805 m) : NeverHalts m :=
  zipCycle_sound p805 11 7 false (1) (by decide) cert805 m hm
#print axioms never805


/-- Third-level first-hole refinement 806, 1RB0RA_1RC0LD_0RD0LA_1LD1RB_------_------; entry 0, period 11. -/
def p806 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert806 : zipCycle p806 0 11 true (0) = true := by decide +kernel
theorem never806 (m : Machine) (hm : compatible p806 m) : NeverHalts m :=
  zipCycle_sound p806 0 11 true (0) (by decide) cert806 m hm
#print axioms never806


/-- Third-level first-hole refinement 807, 1RB1RA_1RC0LD_0RD0LA_1LD1RB_------_------; entry 0, period 11. -/
def p807 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert807 : zipCycle p807 0 11 true (0) = true := by decide +kernel
theorem never807 (m : Machine) (hm : compatible p807 m) : NeverHalts m :=
  zipCycle_sound p807 0 11 true (0) (by decide) cert807 m hm
#print axioms never807


/-- Third-level first-hole refinement 808, 1RB0LB_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 12. -/
def p808 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert808 : zipCycle p808 1 12 true (0) = true := by decide +kernel
theorem never808 (m : Machine) (hm : compatible p808 m) : NeverHalts m :=
  zipCycle_sound p808 1 12 true (0) (by decide) cert808 m hm
#print axioms never808


/-- Third-level first-hole refinement 809, 1RB1LB_1RC0LD_0RD0LA_1LD1RB_------_------; entry 17, period 1. -/
def p809 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert809 : zipCycle p809 17 1 false (-1) = true := by decide +kernel
theorem never809 (m : Machine) (hm : compatible p809 m) : NeverHalts m :=
  zipCycle_sound p809 17 1 false (-1) (by decide) cert809 m hm
#print axioms never809


/-- Third-level first-hole refinement 810, 1RB0RB_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 10. -/
def p810 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert810 : zipCycle p810 1 10 true (1) = true := by decide +kernel
theorem never810 (m : Machine) (hm : compatible p810 m) : NeverHalts m :=
  zipCycle_sound p810 1 10 true (1) (by decide) cert810 m hm
#print axioms never810


/-- Third-level first-hole refinement 811, 1RB1RB_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 10. -/
def p811 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert811 : zipCycle p811 1 10 true (1) = true := by decide +kernel
theorem never811 (m : Machine) (hm : compatible p811 m) : NeverHalts m :=
  zipCycle_sound p811 1 10 true (1) (by decide) cert811 m hm
#print axioms never811


/-- Third-level first-hole refinement 812, 1RB0LC_1RC0LD_0RD0LA_1LD1RB_------_------; entry 14, period 1. -/
def p812 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert812 : zipCycle p812 14 1 false (0) = true := by decide +kernel
theorem never812 (m : Machine) (hm : compatible p812 m) : NeverHalts m :=
  zipCycle_sound p812 14 1 false (0) (by decide) cert812 m hm
#print axioms never812


/-- Third-level first-hole refinement 813, 1RB1LC_1RC0LD_0RD0LA_1LD1RB_------_------; entry 15, period 5. -/
def p813 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert813 : zipCycle p813 15 5 false (2) = true := by decide +kernel
theorem never813 (m : Machine) (hm : compatible p813 m) : NeverHalts m :=
  zipCycle_sound p813 15 5 false (2) (by decide) cert813 m hm
#print axioms never813


/-- Third-level first-hole refinement 814, 1RB0RC_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 22. -/
def p814 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert814 : zipCycle p814 1 22 true (1) = true := by decide +kernel
theorem never814 (m : Machine) (hm : compatible p814 m) : NeverHalts m :=
  zipCycle_sound p814 1 22 true (1) (by decide) cert814 m hm
#print axioms never814


/-- Third-level first-hole refinement 815, 1RB1RC_1RC0LD_0RD0LA_1LD1RB_------_------; entry 2, period 9. -/
def p815 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert815 : zipCycle p815 2 9 true (1) = true := by decide +kernel
theorem never815 (m : Machine) (hm : compatible p815 m) : NeverHalts m :=
  zipCycle_sound p815 2 9 true (1) (by decide) cert815 m hm
#print axioms never815


/-- Third-level first-hole refinement 816, 1RB0LD_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 11. -/
def p816 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert816 : zipCycle p816 1 11 true (1) = true := by decide +kernel
theorem never816 (m : Machine) (hm : compatible p816 m) : NeverHalts m :=
  zipCycle_sound p816 1 11 true (1) (by decide) cert816 m hm
#print axioms never816


/-- Third-level first-hole refinement 817, 1RB1LD_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 13. -/
def p817 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert817 : zipCycle p817 1 13 true (1) = true := by decide +kernel
theorem never817 (m : Machine) (hm : compatible p817 m) : NeverHalts m :=
  zipCycle_sound p817 1 13 true (1) (by decide) cert817 m hm
#print axioms never817


/-- Third-level first-hole refinement 818, 1RB0RD_1RC0LD_0RD0LA_1LD1RB_------_------; entry 3, period 8. -/
def p818 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert818 : zipCycle p818 3 8 true (1) = true := by decide +kernel
theorem never818 (m : Machine) (hm : compatible p818 m) : NeverHalts m :=
  zipCycle_sound p818 3 8 true (1) (by decide) cert818 m hm
#print axioms never818


/-- Third-level first-hole refinement 819, 1RB1RD_1RC0LD_0RD0LA_1LD1RB_------_------; entry 1, period 14. -/
def p819 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert819 : zipCycle p819 1 14 true (1) = true := by decide +kernel
theorem never819 (m : Machine) (hm : compatible p819 m) : NeverHalts m :=
  zipCycle_sound p819 1 14 true (1) (by decide) cert819 m hm
#print axioms never819


/-- Third-level first-hole refinement 820, 1RB0LA_1RC0LD_0RD1LA_1LD1RB_------_------; entry 0, period 13. -/
def p820 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert820 : zipCycle p820 0 13 false (3) = true := by decide +kernel
theorem never820 (m : Machine) (hm : compatible p820 m) : NeverHalts m :=
  zipCycle_sound p820 0 13 false (3) (by decide) cert820 m hm
#print axioms never820


/-- Third-level first-hole refinement 821, 1RB1LA_1RC0LD_0RD1LA_1LD1RB_------_------; entry 11, period 7. -/
def p821 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert821 : zipCycle p821 11 7 false (1) = true := by decide +kernel
theorem never821 (m : Machine) (hm : compatible p821 m) : NeverHalts m :=
  zipCycle_sound p821 11 7 false (1) (by decide) cert821 m hm
#print axioms never821


/-- Third-level first-hole refinement 822, 1RB0RA_1RC0LD_0RD1LA_1LD1RB_------_------; entry 0, period 12. -/
def p822 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert822 : zipCycle p822 0 12 true (0) = true := by decide +kernel
theorem never822 (m : Machine) (hm : compatible p822 m) : NeverHalts m :=
  zipCycle_sound p822 0 12 true (0) (by decide) cert822 m hm
#print axioms never822


/-- Third-level first-hole refinement 823, 1RB1RA_1RC0LD_0RD1LA_1LD1RB_------_------; entry 0, period 12. -/
def p823 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert823 : zipCycle p823 0 12 true (0) = true := by decide +kernel
theorem never823 (m : Machine) (hm : compatible p823 m) : NeverHalts m :=
  zipCycle_sound p823 0 12 true (0) (by decide) cert823 m hm
#print axioms never823


/-- Third-level first-hole refinement 824, 1RB0LB_1RC0LD_0RD1LA_1LD1RB_------_------; entry 1, period 15. -/
def p824 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert824 : zipCycle p824 1 15 true (0) = true := by decide +kernel
theorem never824 (m : Machine) (hm : compatible p824 m) : NeverHalts m :=
  zipCycle_sound p824 1 15 true (0) (by decide) cert824 m hm
#print axioms never824


/-- Third-level first-hole refinement 825, 1RB1LB_1RC0LD_0RD1LA_1LD1RB_------_------; entry 17, period 1. -/
def p825 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert825 : zipCycle p825 17 1 false (-1) = true := by decide +kernel
theorem never825 (m : Machine) (hm : compatible p825 m) : NeverHalts m :=
  zipCycle_sound p825 17 1 false (-1) (by decide) cert825 m hm
#print axioms never825


/-- Third-level first-hole refinement 826, 1RB0RB_1RC0LD_0RD1LA_1LD1RB_------_------; entry 1, period 15. -/
def p826 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert826 : zipCycle p826 1 15 true (1) = true := by decide +kernel
theorem never826 (m : Machine) (hm : compatible p826 m) : NeverHalts m :=
  zipCycle_sound p826 1 15 true (1) (by decide) cert826 m hm
#print axioms never826


/-- Third-level first-hole refinement 827, 1RB1RB_1RC0LD_0RD1LA_1LD1RB_------_------; entry 1, period 12. -/
def p827 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert827 : zipCycle p827 1 12 true (1) = true := by decide +kernel
theorem never827 (m : Machine) (hm : compatible p827 m) : NeverHalts m :=
  zipCycle_sound p827 1 12 true (1) (by decide) cert827 m hm
#print axioms never827


/-- Third-level first-hole refinement 828, 1RB0LC_1RC0LD_0RD1LA_1LD1RB_------_------; entry 14, period 1. -/
def p828 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert828 : zipCycle p828 14 1 false (0) = true := by decide +kernel
theorem never828 (m : Machine) (hm : compatible p828 m) : NeverHalts m :=
  zipCycle_sound p828 14 1 false (0) (by decide) cert828 m hm
#print axioms never828


/-- Third-level first-hole refinement 829, 1RB1LC_1RC0LD_0RD1LA_1LD1RB_------_------; entry 15, period 7. -/
def p829 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert829 : zipCycle p829 15 7 false (2) = true := by decide +kernel
theorem never829 (m : Machine) (hm : compatible p829 m) : NeverHalts m :=
  zipCycle_sound p829 15 7 false (2) (by decide) cert829 m hm
#print axioms never829


/-- Third-level first-hole refinement 830, 1RB0RC_1RC0LD_0RD1LA_1LD1RB_------_------; entry 1, period 14. -/
def p830 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert830 : zipCycle p830 1 14 true (1) = true := by decide +kernel
theorem never830 (m : Machine) (hm : compatible p830 m) : NeverHalts m :=
  zipCycle_sound p830 1 14 true (1) (by decide) cert830 m hm
#print axioms never830


/-- Third-level first-hole refinement 831, 1RB1RC_1RC0LD_0RD1LA_1LD1RB_------_------; entry 9, period 2. -/
def p831 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert831 : zipCycle p831 9 2 true (2) = true := by decide +kernel
theorem never831 (m : Machine) (hm : compatible p831 m) : NeverHalts m :=
  zipCycle_sound p831 9 2 true (2) (by decide) cert831 m hm
#print axioms never831


/-- Third-level first-hole refinement 832, 1RB0LD_1RC0LD_0RD1LA_1LD1RB_------_------; entry 7, period 4. -/
def p832 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert832 : zipCycle p832 7 4 true (1) = true := by decide +kernel
theorem never832 (m : Machine) (hm : compatible p832 m) : NeverHalts m :=
  zipCycle_sound p832 7 4 true (1) (by decide) cert832 m hm
#print axioms never832


/-- Third-level first-hole refinement 833, 1RB1LD_1RC0LD_0RD1LA_1LD1RB_------_------; entry 5, period 6. -/
def p833 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert833 : zipCycle p833 5 6 true (1) = true := by decide +kernel
theorem never833 (m : Machine) (hm : compatible p833 m) : NeverHalts m :=
  zipCycle_sound p833 5 6 true (1) (by decide) cert833 m hm
#print axioms never833


/-- Third-level first-hole refinement 834, 1RB0RD_1RC0LD_0RD1LA_1LD1RB_------_------; entry 1, period 11. -/
def p834 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert834 : zipCycle p834 1 11 true (1) = true := by decide +kernel
theorem never834 (m : Machine) (hm : compatible p834 m) : NeverHalts m :=
  zipCycle_sound p834 1 11 true (1) (by decide) cert834 m hm
#print axioms never834


/-- Third-level first-hole refinement 835, 1RB1RD_1RC0LD_0RD1LA_1LD1RB_------_------; entry 1, period 11. -/
def p835 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert835 : zipCycle p835 1 11 true (1) = true := by decide +kernel
theorem never835 (m : Machine) (hm : compatible p835 m) : NeverHalts m :=
  zipCycle_sound p835 1 11 true (1) (by decide) cert835 m hm
#print axioms never835


/-- Third-level first-hole refinement 836, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0RA_------; entry 0, period 11. -/
def p836 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert836 : zipCycle p836 0 11 true (0) = true := by decide +kernel
theorem never836 (m : Machine) (hm : compatible p836 m) : NeverHalts m :=
  zipCycle_sound p836 0 11 true (0) (by decide) cert836 m hm
#print axioms never836


/-- Third-level first-hole refinement 837, 1RB---_1RC0LD_0RD0LE_1LD1RB_---1RA_------; entry 0, period 11. -/
def p837 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert837 : zipCycle p837 0 11 true (0) = true := by decide +kernel
theorem never837 (m : Machine) (hm : compatible p837 m) : NeverHalts m :=
  zipCycle_sound p837 0 11 true (0) (by decide) cert837 m hm
#print axioms never837


/-- Third-level first-hole refinement 838, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0LB_------; entry 1, period 12. -/
def p838 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert838 : zipCycle p838 1 12 true (0) = true := by decide +kernel
theorem never838 (m : Machine) (hm : compatible p838 m) : NeverHalts m :=
  zipCycle_sound p838 1 12 true (0) (by decide) cert838 m hm
#print axioms never838


/-- Third-level first-hole refinement 839, 1RB---_1RC0LD_0RD0LE_1LD1RB_---1LB_------; entry 17, period 1. -/
def p839 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert839 : zipCycle p839 17 1 false (-1) = true := by decide +kernel
theorem never839 (m : Machine) (hm : compatible p839 m) : NeverHalts m :=
  zipCycle_sound p839 17 1 false (-1) (by decide) cert839 m hm
#print axioms never839


/-- Third-level first-hole refinement 840, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0RB_------; entry 1, period 10. -/
def p840 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert840 : zipCycle p840 1 10 true (1) = true := by decide +kernel
theorem never840 (m : Machine) (hm : compatible p840 m) : NeverHalts m :=
  zipCycle_sound p840 1 10 true (1) (by decide) cert840 m hm
#print axioms never840


/-- Third-level first-hole refinement 841, 1RB---_1RC0LD_0RD0LE_1LD1RB_---1RB_------; entry 1, period 10. -/
def p841 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert841 : zipCycle p841 1 10 true (1) = true := by decide +kernel
theorem never841 (m : Machine) (hm : compatible p841 m) : NeverHalts m :=
  zipCycle_sound p841 1 10 true (1) (by decide) cert841 m hm
#print axioms never841


/-- Third-level first-hole refinement 842, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0LC_------; entry 14, period 1. -/
def p842 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert842 : zipCycle p842 14 1 false (0) = true := by decide +kernel
theorem never842 (m : Machine) (hm : compatible p842 m) : NeverHalts m :=
  zipCycle_sound p842 14 1 false (0) (by decide) cert842 m hm
#print axioms never842


/-- Third-level first-hole refinement 843, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0RC_------; entry 1, period 22. -/
def p843 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert843 : zipCycle p843 1 22 true (1) = true := by decide +kernel
theorem never843 (m : Machine) (hm : compatible p843 m) : NeverHalts m :=
  zipCycle_sound p843 1 22 true (1) (by decide) cert843 m hm
#print axioms never843


/-- Third-level first-hole refinement 844, 1RB---_1RC0LD_0RD0LE_1LD1RB_---1RC_------; entry 2, period 9. -/
def p844 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert844 : zipCycle p844 2 9 true (1) = true := by decide +kernel
theorem never844 (m : Machine) (hm : compatible p844 m) : NeverHalts m :=
  zipCycle_sound p844 2 9 true (1) (by decide) cert844 m hm
#print axioms never844


/-- Third-level first-hole refinement 845, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0LD_------; entry 1, period 11. -/
def p845 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert845 : zipCycle p845 1 11 true (1) = true := by decide +kernel
theorem never845 (m : Machine) (hm : compatible p845 m) : NeverHalts m :=
  zipCycle_sound p845 1 11 true (1) (by decide) cert845 m hm
#print axioms never845


/-- Third-level first-hole refinement 846, 1RB---_1RC0LD_0RD0LE_1LD1RB_---1LD_------; entry 1, period 13. -/
def p846 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert846 : zipCycle p846 1 13 true (1) = true := by decide +kernel
theorem never846 (m : Machine) (hm : compatible p846 m) : NeverHalts m :=
  zipCycle_sound p846 1 13 true (1) (by decide) cert846 m hm
#print axioms never846


/-- Third-level first-hole refinement 847, 1RB---_1RC0LD_0RD0LE_1LD1RB_---0RD_------; entry 3, period 8. -/
def p847 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert847 : zipCycle p847 3 8 true (1) = true := by decide +kernel
theorem never847 (m : Machine) (hm : compatible p847 m) : NeverHalts m :=
  zipCycle_sound p847 3 8 true (1) (by decide) cert847 m hm
#print axioms never847


/-- Third-level first-hole refinement 848, 1RB---_1RC0LD_0RD0LE_1LD1RB_---1RD_------; entry 1, period 14. -/
def p848 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert848 : zipCycle p848 1 14 true (1) = true := by decide +kernel
theorem never848 (m : Machine) (hm : compatible p848 m) : NeverHalts m :=
  zipCycle_sound p848 1 14 true (1) (by decide) cert848 m hm
#print axioms never848


/-- Third-level first-hole refinement 849, 1RB---_1RC0LD_0RD1LE_1LD1RB_---0LB_------; entry 1, period 15. -/
def p849 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert849 : zipCycle p849 1 15 true (0) = true := by decide +kernel
theorem never849 (m : Machine) (hm : compatible p849 m) : NeverHalts m :=
  zipCycle_sound p849 1 15 true (0) (by decide) cert849 m hm
#print axioms never849


/-- Third-level first-hole refinement 850, 1RB---_1RC0LD_0RD1LE_1LD1RB_---1LB_------; entry 17, period 1. -/
def p850 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert850 : zipCycle p850 17 1 false (-1) = true := by decide +kernel
theorem never850 (m : Machine) (hm : compatible p850 m) : NeverHalts m :=
  zipCycle_sound p850 17 1 false (-1) (by decide) cert850 m hm
#print axioms never850


/-- Third-level first-hole refinement 851, 1RB---_1RC0LD_0RD1LE_1LD1RB_---0RB_------; entry 1, period 15. -/
def p851 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert851 : zipCycle p851 1 15 true (1) = true := by decide +kernel
theorem never851 (m : Machine) (hm : compatible p851 m) : NeverHalts m :=
  zipCycle_sound p851 1 15 true (1) (by decide) cert851 m hm
#print axioms never851


/-- Third-level first-hole refinement 852, 1RB---_1RC0LD_0RD1LE_1LD1RB_---1RB_------; entry 1, period 12. -/
def p852 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert852 : zipCycle p852 1 12 true (1) = true := by decide +kernel
theorem never852 (m : Machine) (hm : compatible p852 m) : NeverHalts m :=
  zipCycle_sound p852 1 12 true (1) (by decide) cert852 m hm
#print axioms never852


/-- Third-level first-hole refinement 853, 1RB---_1RC0LD_0RD1LE_1LD1RB_---0LC_------; entry 14, period 1. -/
def p853 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert853 : zipCycle p853 14 1 false (0) = true := by decide +kernel
theorem never853 (m : Machine) (hm : compatible p853 m) : NeverHalts m :=
  zipCycle_sound p853 14 1 false (0) (by decide) cert853 m hm
#print axioms never853


/-- Third-level first-hole refinement 854, 1RB---_1RC0LD_0RD1LE_1LD1RB_---1RC_------; entry 9, period 2. -/
def p854 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert854 : zipCycle p854 9 2 true (2) = true := by decide +kernel
theorem never854 (m : Machine) (hm : compatible p854 m) : NeverHalts m :=
  zipCycle_sound p854 9 2 true (2) (by decide) cert854 m hm
#print axioms never854


/-- Third-level first-hole refinement 855, 1RB---_1RC0LD_0RD1LE_1LD1RB_---0LD_------; entry 7, period 4. -/
def p855 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert855 : zipCycle p855 7 4 true (1) = true := by decide +kernel
theorem never855 (m : Machine) (hm : compatible p855 m) : NeverHalts m :=
  zipCycle_sound p855 7 4 true (1) (by decide) cert855 m hm
#print axioms never855


/-- Third-level first-hole refinement 856, 1RB---_1RC0LD_0RD1LE_1LD1RB_---1LD_------; entry 5, period 6. -/
def p856 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert856 : zipCycle p856 5 6 true (1) = true := by decide +kernel
theorem never856 (m : Machine) (hm : compatible p856 m) : NeverHalts m :=
  zipCycle_sound p856 5 6 true (1) (by decide) cert856 m hm
#print axioms never856


/-- Third-level first-hole refinement 857, 1RB---_1RC0LD_0RD1LE_1LD1RB_---0RD_------; entry 1, period 11. -/
def p857 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert857 : zipCycle p857 1 11 true (1) = true := by decide +kernel
theorem never857 (m : Machine) (hm : compatible p857 m) : NeverHalts m :=
  zipCycle_sound p857 1 11 true (1) (by decide) cert857 m hm
#print axioms never857


/-- Third-level first-hole refinement 858, 1RB---_1RC0LD_0RD1LE_1LD1RB_---1RD_------; entry 1, period 11. -/
def p858 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert858 : zipCycle p858 1 11 true (1) = true := by decide +kernel
theorem never858 (m : Machine) (hm : compatible p858 m) : NeverHalts m :=
  zipCycle_sound p858 1 11 true (1) (by decide) cert858 m hm
#print axioms never858


/-- Third-level first-hole refinement 859, 1RB---_1RC0LD_0RD0RE_1LD1RB_0LA---_------; entry 0, period 11. -/
def p859 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert859 : zipCycle p859 0 11 true (0) = true := by decide +kernel
theorem never859 (m : Machine) (hm : compatible p859 m) : NeverHalts m :=
  zipCycle_sound p859 0 11 true (0) (by decide) cert859 m hm
#print axioms never859


/-- Third-level first-hole refinement 860, 1RB---_1RC0LD_0RD0RE_1LD1RB_1LA---_------; entry 1, period 13. -/
def p860 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert860 : zipCycle p860 1 13 true (1) = true := by decide +kernel
theorem never860 (m : Machine) (hm : compatible p860 m) : NeverHalts m :=
  zipCycle_sound p860 1 13 true (1) (by decide) cert860 m hm
#print axioms never860


/-- Third-level first-hole refinement 861, 1RB---_1RC0LD_0RD0RE_1LD1RB_0RA---_------; entry 0, period 11. -/
def p861 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert861 : zipCycle p861 0 11 true (0) = true := by decide +kernel
theorem never861 (m : Machine) (hm : compatible p861 m) : NeverHalts m :=
  zipCycle_sound p861 0 11 true (0) (by decide) cert861 m hm
#print axioms never861


/-- Third-level first-hole refinement 862, 1RB---_1RC0LD_0RD0RE_1LD1RB_1RA---_------; entry 0, period 11. -/
def p862 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert862 : zipCycle p862 0 11 true (0) = true := by decide +kernel
theorem never862 (m : Machine) (hm : compatible p862 m) : NeverHalts m :=
  zipCycle_sound p862 0 11 true (0) (by decide) cert862 m hm
#print axioms never862


/-- Third-level first-hole refinement 863, 1RB---_1RC0LD_0RD0RE_1LD1RB_0LB---_------; entry 1, period 10. -/
def p863 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert863 : zipCycle p863 1 10 true (1) = true := by decide +kernel
theorem never863 (m : Machine) (hm : compatible p863 m) : NeverHalts m :=
  zipCycle_sound p863 1 10 true (1) (by decide) cert863 m hm
#print axioms never863


/-- Third-level first-hole refinement 864, 1RB---_1RC0LD_0RD0RE_1LD1RB_1LB---_------; entry 8, period 3. -/
def p864 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert864 : zipCycle p864 8 3 true (2) = true := by decide +kernel
theorem never864 (m : Machine) (hm : compatible p864 m) : NeverHalts m :=
  zipCycle_sound p864 8 3 true (2) (by decide) cert864 m hm
#print axioms never864


/-- Third-level first-hole refinement 865, 1RB---_1RC0LD_0RD0RE_1LD1RB_0RB---_------; entry 1, period 10. -/
def p865 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert865 : zipCycle p865 1 10 true (1) = true := by decide +kernel
theorem never865 (m : Machine) (hm : compatible p865 m) : NeverHalts m :=
  zipCycle_sound p865 1 10 true (1) (by decide) cert865 m hm
#print axioms never865


/-- Third-level first-hole refinement 866, 1RB---_1RC0LD_0RD0RE_1LD1RB_1RB---_------; entry 1, period 10. -/
def p866 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert866 : zipCycle p866 1 10 true (1) = true := by decide +kernel
theorem never866 (m : Machine) (hm : compatible p866 m) : NeverHalts m :=
  zipCycle_sound p866 1 10 true (1) (by decide) cert866 m hm
#print axioms never866


/-- Third-level first-hole refinement 867, 1RB---_1RC0LD_0RD0RE_1LD1RB_0LC---_------; entry 2, period 9. -/
def p867 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert867 : zipCycle p867 2 9 true (1) = true := by decide +kernel
theorem never867 (m : Machine) (hm : compatible p867 m) : NeverHalts m :=
  zipCycle_sound p867 2 9 true (1) (by decide) cert867 m hm
#print axioms never867


/-- Third-level first-hole refinement 868, 1RB---_1RC0LD_0RD0RE_1LD1RB_1LC---_------; entry 1, period 12. -/
def p868 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert868 : zipCycle p868 1 12 true (1) = true := by decide +kernel
theorem never868 (m : Machine) (hm : compatible p868 m) : NeverHalts m :=
  zipCycle_sound p868 1 12 true (1) (by decide) cert868 m hm
#print axioms never868


/-- Third-level first-hole refinement 869, 1RB---_1RC0LD_0RD0RE_1LD1RB_1RC---_------; entry 2, period 9. -/
def p869 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert869 : zipCycle p869 2 9 true (1) = true := by decide +kernel
theorem never869 (m : Machine) (hm : compatible p869 m) : NeverHalts m :=
  zipCycle_sound p869 2 9 true (1) (by decide) cert869 m hm
#print axioms never869


/-- Third-level first-hole refinement 870, 1RB---_1RC0LD_0RD0RE_1LD1RB_0LD---_------; entry 1, period 14. -/
def p870 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert870 : zipCycle p870 1 14 true (1) = true := by decide +kernel
theorem never870 (m : Machine) (hm : compatible p870 m) : NeverHalts m :=
  zipCycle_sound p870 1 14 true (1) (by decide) cert870 m hm
#print axioms never870


/-- Third-level first-hole refinement 871, 1RB---_1RC0LD_0RD0RE_1LD1RB_1LD---_------; entry 4, period 7. -/
def p871 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert871 : zipCycle p871 4 7 true (1) = true := by decide +kernel
theorem never871 (m : Machine) (hm : compatible p871 m) : NeverHalts m :=
  zipCycle_sound p871 4 7 true (1) (by decide) cert871 m hm
#print axioms never871


/-- Third-level first-hole refinement 872, 1RB---_1RC0LD_0RD0RE_1LD1RB_1RD---_------; entry 1, period 14. -/
def p872 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert872 : zipCycle p872 1 14 true (1) = true := by decide +kernel
theorem never872 (m : Machine) (hm : compatible p872 m) : NeverHalts m :=
  zipCycle_sound p872 1 14 true (1) (by decide) cert872 m hm
#print axioms never872


/-- Third-level first-hole refinement 873, 1RB---_1RC0LD_0RD0RE_1LD1RB_0RE---_------; entry 10, period 1. -/
def p873 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert873 : zipCycle p873 10 1 true (4) = true := by decide +kernel
theorem never873 (m : Machine) (hm : compatible p873 m) : NeverHalts m :=
  zipCycle_sound p873 10 1 true (4) (by decide) cert873 m hm
#print axioms never873


/-- Third-level first-hole refinement 874, 1RB---_1RC0LD_0RD0RE_1LD1RB_1RE---_------; entry 10, period 1. -/
def p874 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert874 : zipCycle p874 10 1 true (4) = true := by decide +kernel
theorem never874 (m : Machine) (hm : compatible p874 m) : NeverHalts m :=
  zipCycle_sound p874 10 1 true (4) (by decide) cert874 m hm
#print axioms never874


/-- Third-level first-hole refinement 875, 1RB---_1RC0LD_0RD1RE_1LD1RB_0RA---_------; entry 0, period 11. -/
def p875 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem cert875 : zipCycle p875 0 11 true (0) = true := by decide +kernel
theorem never875 (m : Machine) (hm : compatible p875 m) : NeverHalts m :=
  zipCycle_sound p875 0 11 true (0) (by decide) cert875 m hm
#print axioms never875


/-- Third-level first-hole refinement 876, 1RB---_1RC0LD_0RD1RE_1LD1RB_1RA---_------; entry 0, period 11. -/
def p876 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | _,_ => none
theorem cert876 : zipCycle p876 0 11 true (0) = true := by decide +kernel
theorem never876 (m : Machine) (hm : compatible p876 m) : NeverHalts m :=
  zipCycle_sound p876 0 11 true (0) (by decide) cert876 m hm
#print axioms never876


/-- Third-level first-hole refinement 877, 1RB---_1RC0LD_0RD1RE_1LD1RB_0LB---_------; entry 1, period 12. -/
def p877 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert877 : zipCycle p877 1 12 true (1) = true := by decide +kernel
theorem never877 (m : Machine) (hm : compatible p877 m) : NeverHalts m :=
  zipCycle_sound p877 1 12 true (1) (by decide) cert877 m hm
#print axioms never877


/-- Third-level first-hole refinement 878, 1RB---_1RC0LD_0RD1RE_1LD1RB_1LB---_------; entry 6, period 5. -/
def p878 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert878 : zipCycle p878 6 5 true (1) = true := by decide +kernel
theorem never878 (m : Machine) (hm : compatible p878 m) : NeverHalts m :=
  zipCycle_sound p878 6 5 true (1) (by decide) cert878 m hm
#print axioms never878


/-- Third-level first-hole refinement 879, 1RB---_1RC0LD_0RD1RE_1LD1RB_0RB---_------; entry 1, period 10. -/
def p879 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert879 : zipCycle p879 1 10 true (1) = true := by decide +kernel
theorem never879 (m : Machine) (hm : compatible p879 m) : NeverHalts m :=
  zipCycle_sound p879 1 10 true (1) (by decide) cert879 m hm
#print axioms never879


/-- Third-level first-hole refinement 880, 1RB---_1RC0LD_0RD1RE_1LD1RB_1RB---_------; entry 1, period 10. -/
def p880 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert880 : zipCycle p880 1 10 true (1) = true := by decide +kernel
theorem never880 (m : Machine) (hm : compatible p880 m) : NeverHalts m :=
  zipCycle_sound p880 1 10 true (1) (by decide) cert880 m hm
#print axioms never880


/-- Third-level first-hole refinement 881, 1RB---_1RC0LD_0RD1RE_1LD1RB_0LC---_------; entry 9, period 2. -/
def p881 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert881 : zipCycle p881 9 2 true (3) = true := by decide +kernel
theorem never881 (m : Machine) (hm : compatible p881 m) : NeverHalts m :=
  zipCycle_sound p881 9 2 true (3) (by decide) cert881 m hm
#print axioms never881


/-- Third-level first-hole refinement 882, 1RB---_1RC0LD_0RD1RE_1LD1RB_1RC---_------; entry 2, period 9. -/
def p882 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | _,_ => none
theorem cert882 : zipCycle p882 2 9 true (1) = true := by decide +kernel
theorem never882 (m : Machine) (hm : compatible p882 m) : NeverHalts m :=
  zipCycle_sound p882 2 9 true (1) (by decide) cert882 m hm
#print axioms never882


/-- Third-level first-hole refinement 883, 1RB---_1RC0LD_0RD1RE_1LD1RB_0LD---_------; entry 1, period 11. -/
def p883 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert883 : zipCycle p883 1 11 true (1) = true := by decide +kernel
theorem never883 (m : Machine) (hm : compatible p883 m) : NeverHalts m :=
  zipCycle_sound p883 1 11 true (1) (by decide) cert883 m hm
#print axioms never883


/-- Third-level first-hole refinement 884, 1RB---_1RC0LD_0RD1RE_1LD1RB_1LD---_------; entry 1, period 13. -/
def p884 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | _,_ => none
theorem cert884 : zipCycle p884 1 13 true (1) = true := by decide +kernel
theorem never884 (m : Machine) (hm : compatible p884 m) : NeverHalts m :=
  zipCycle_sound p884 1 13 true (1) (by decide) cert884 m hm
#print axioms never884


/-- Third-level first-hole refinement 885, 1RB---_1RC0LD_0RD1RE_1LD1RB_0RD---_------; entry 3, period 8. -/
def p885 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem cert885 : zipCycle p885 3 8 true (1) = true := by decide +kernel
theorem never885 (m : Machine) (hm : compatible p885 m) : NeverHalts m :=
  zipCycle_sound p885 3 8 true (1) (by decide) cert885 m hm
#print axioms never885


/-- Third-level first-hole refinement 886, 1RB---_1RC0LD_0RD1RE_1LD1RB_1RD---_------; entry 1, period 14. -/
def p886 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert886 : zipCycle p886 1 14 true (1) = true := by decide +kernel
theorem never886 (m : Machine) (hm : compatible p886 m) : NeverHalts m :=
  zipCycle_sound p886 1 14 true (1) (by decide) cert886 m hm
#print axioms never886


/-- Third-level first-hole refinement 887, 1RB---_1RC0LD_0RD1RE_1LD1RB_0RE---_------; entry 10, period 1. -/
def p887 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert887 : zipCycle p887 10 1 true (4) = true := by decide +kernel
theorem never887 (m : Machine) (hm : compatible p887 m) : NeverHalts m :=
  zipCycle_sound p887 10 1 true (4) (by decide) cert887 m hm
#print axioms never887


/-- Third-level first-hole refinement 888, 1RB---_1RC0LD_0RD1RE_1LD1RB_1RE---_------; entry 10, period 1. -/
def p888 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,3⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert888 : zipCycle p888 10 1 true (4) = true := by decide +kernel
theorem never888 (m : Machine) (hm : compatible p888 m) : NeverHalts m :=
  zipCycle_sound p888 10 1 true (4) (by decide) cert888 m hm
#print axioms never888


/-- Third-level first-hole refinement 889, 1RB0LA_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 0, period 9. -/
def p889 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert889 : zipCycle p889 0 9 false (3) = true := by decide +kernel
theorem never889 (m : Machine) (hm : compatible p889 m) : NeverHalts m :=
  zipCycle_sound p889 0 9 false (3) (by decide) cert889 m hm
#print axioms never889


/-- Third-level first-hole refinement 890, 1RB1LA_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 0, period 12. -/
def p890 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert890 : zipCycle p890 0 12 false (3) = true := by decide +kernel
theorem never890 (m : Machine) (hm : compatible p890 m) : NeverHalts m :=
  zipCycle_sound p890 0 12 false (3) (by decide) cert890 m hm
#print axioms never890


/-- Third-level first-hole refinement 891, 1RB0RB_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 1, period 11. -/
def p891 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert891 : zipCycle p891 1 11 true (0) = true := by decide +kernel
theorem never891 (m : Machine) (hm : compatible p891 m) : NeverHalts m :=
  zipCycle_sound p891 1 11 true (0) (by decide) cert891 m hm
#print axioms never891


/-- Third-level first-hole refinement 892, 1RB1RB_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 1, period 11. -/
def p892 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert892 : zipCycle p892 1 11 true (0) = true := by decide +kernel
theorem never892 (m : Machine) (hm : compatible p892 m) : NeverHalts m :=
  zipCycle_sound p892 1 11 true (0) (by decide) cert892 m hm
#print axioms never892


/-- Third-level first-hole refinement 893, 1RB0LC_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 10, period 1. -/
def p893 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert893 : zipCycle p893 10 1 false (0) = true := by decide +kernel
theorem never893 (m : Machine) (hm : compatible p893 m) : NeverHalts m :=
  zipCycle_sound p893 10 1 false (0) (by decide) cert893 m hm
#print axioms never893


/-- Third-level first-hole refinement 894, 1RB1LC_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 1, period 13. -/
def p894 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert894 : zipCycle p894 1 13 true (-1) = true := by decide +kernel
theorem never894 (m : Machine) (hm : compatible p894 m) : NeverHalts m :=
  zipCycle_sound p894 1 13 true (-1) (by decide) cert894 m hm
#print axioms never894


/-- Third-level first-hole refinement 895, 1RB0RC_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 10, period 1. -/
def p895 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert895 : zipCycle p895 10 1 false (2) = true := by decide +kernel
theorem never895 (m : Machine) (hm : compatible p895 m) : NeverHalts m :=
  zipCycle_sound p895 10 1 false (2) (by decide) cert895 m hm
#print axioms never895


/-- Third-level first-hole refinement 896, 1RB0LD_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 9, period 1. -/
def p896 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert896 : zipCycle p896 9 1 false (-1) = true := by decide +kernel
theorem never896 (m : Machine) (hm : compatible p896 m) : NeverHalts m :=
  zipCycle_sound p896 9 1 false (-1) (by decide) cert896 m hm
#print axioms never896


/-- Third-level first-hole refinement 897, 1RB1LD_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 9, period 1. -/
def p897 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert897 : zipCycle p897 9 1 false (-1) = true := by decide +kernel
theorem never897 (m : Machine) (hm : compatible p897 m) : NeverHalts m :=
  zipCycle_sound p897 9 1 false (-1) (by decide) cert897 m hm
#print axioms never897


/-- Third-level first-hole refinement 898, 1RB0RD_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 9, period 1. -/
def p898 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert898 : zipCycle p898 9 1 false (1) = true := by decide +kernel
theorem never898 (m : Machine) (hm : compatible p898 m) : NeverHalts m :=
  zipCycle_sound p898 9 1 false (1) (by decide) cert898 m hm
#print axioms never898


/-- Third-level first-hole refinement 899, 1RB1RD_1RC0LE_0RD---_1LD1RB_---0LA_------; entry 0, period 13. -/
def p899 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,0⟩)
  | _,_ => none
theorem cert899 : zipCycle p899 0 13 false (3) = true := by decide +kernel
theorem never899 (m : Machine) (hm : compatible p899 m) : NeverHalts m :=
  zipCycle_sound p899 0 13 false (3) (by decide) cert899 m hm
#print axioms never899

end BB6.Agent24Raw45D3_08
