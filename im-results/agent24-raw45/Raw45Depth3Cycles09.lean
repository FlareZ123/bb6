import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_09
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 900, 1RB1LA_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 9, period 3. -/
def p900 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert900 : zipCycle p900 9 3 false (0) = true := by decide +kernel
theorem never900 (m : Machine) (hm : compatible p900 m) : NeverHalts m :=
  zipCycle_sound p900 9 3 false (0) (by decide) cert900 m hm
#print axioms never900


/-- Third-level first-hole refinement 901, 1RB0RA_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 10, period 3. -/
def p901 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert901 : zipCycle p901 10 3 false (3) = true := by decide +kernel
theorem never901 (m : Machine) (hm : compatible p901 m) : NeverHalts m :=
  zipCycle_sound p901 10 3 false (3) (by decide) cert901 m hm
#print axioms never901


/-- Third-level first-hole refinement 902, 1RB1RA_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 0, period 15. -/
def p902 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,0⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert902 : zipCycle p902 0 15 true (0) = true := by decide +kernel
theorem never902 (m : Machine) (hm : compatible p902 m) : NeverHalts m :=
  zipCycle_sound p902 0 15 true (0) (by decide) cert902 m hm
#print axioms never902


/-- Third-level first-hole refinement 903, 1RB1RB_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 9, period 3. -/
def p903 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert903 : zipCycle p903 9 3 false (1) = true := by decide +kernel
theorem never903 (m : Machine) (hm : compatible p903 m) : NeverHalts m :=
  zipCycle_sound p903 9 3 false (1) (by decide) cert903 m hm
#print axioms never903


/-- Third-level first-hole refinement 904, 1RB0LC_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 10, period 1. -/
def p904 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert904 : zipCycle p904 10 1 false (0) = true := by decide +kernel
theorem never904 (m : Machine) (hm : compatible p904 m) : NeverHalts m :=
  zipCycle_sound p904 10 1 false (0) (by decide) cert904 m hm
#print axioms never904


/-- Third-level first-hole refinement 905, 1RB1LC_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 11, period 3. -/
def p905 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,2⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert905 : zipCycle p905 11 3 false (1) = true := by decide +kernel
theorem never905 (m : Machine) (hm : compatible p905 m) : NeverHalts m :=
  zipCycle_sound p905 11 3 false (1) (by decide) cert905 m hm
#print axioms never905


/-- Third-level first-hole refinement 906, 1RB0LD_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 9, period 1. -/
def p906 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert906 : zipCycle p906 9 1 false (-1) = true := by decide +kernel
theorem never906 (m : Machine) (hm : compatible p906 m) : NeverHalts m :=
  zipCycle_sound p906 9 1 false (-1) (by decide) cert906 m hm
#print axioms never906


/-- Third-level first-hole refinement 907, 1RB1LD_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 9, period 1. -/
def p907 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,false,3⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert907 : zipCycle p907 9 1 false (-1) = true := by decide +kernel
theorem never907 (m : Machine) (hm : compatible p907 m) : NeverHalts m :=
  zipCycle_sound p907 9 1 false (-1) (by decide) cert907 m hm
#print axioms never907


/-- Third-level first-hole refinement 908, 1RB0RE_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 9, period 3. -/
def p908 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨false,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert908 : zipCycle p908 9 3 false (1) = true := by decide +kernel
theorem never908 (m : Machine) (hm : compatible p908 m) : NeverHalts m :=
  zipCycle_sound p908 9 3 false (1) (by decide) cert908 m hm
#print axioms never908


/-- Third-level first-hole refinement 909, 1RB1RE_1RC0LE_0RD---_1LD1RB_---1LA_------; entry 7, period 2. -/
def p909 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 0, true => some (some ⟨true,true,4⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert909 : zipCycle p909 7 2 true (0) = true := by decide +kernel
theorem never909 (m : Machine) (hm : compatible p909 m) : NeverHalts m :=
  zipCycle_sound p909 7 2 true (0) (by decide) cert909 m hm
#print axioms never909


/-- Third-level first-hole refinement 910, 1RB---_1RC0LE_0RD---_1LD1RB_0LA0LB_------; entry 0, period 10. -/
def p910 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert910 : zipCycle p910 0 10 false (3) = true := by decide +kernel
theorem never910 (m : Machine) (hm : compatible p910 m) : NeverHalts m :=
  zipCycle_sound p910 0 10 false (3) (by decide) cert910 m hm
#print axioms never910


/-- Third-level first-hole refinement 911, 1RB---_1RC0LE_0RD---_1LD1RB_1LA0LB_------; entry 11, period 7. -/
def p911 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert911 : zipCycle p911 11 7 false (-1) = true := by decide +kernel
theorem never911 (m : Machine) (hm : compatible p911 m) : NeverHalts m :=
  zipCycle_sound p911 11 7 false (-1) (by decide) cert911 m hm
#print axioms never911


/-- Third-level first-hole refinement 912, 1RB---_1RC0LE_0RD---_1LD1RB_0RA0LB_------; entry 1, period 13. -/
def p912 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert912 : zipCycle p912 1 13 true (-1) = true := by decide +kernel
theorem never912 (m : Machine) (hm : compatible p912 m) : NeverHalts m :=
  zipCycle_sound p912 1 13 true (-1) (by decide) cert912 m hm
#print axioms never912


/-- Third-level first-hole refinement 913, 1RB---_1RC0LE_0RD---_1LD1RB_1RA0LB_------; entry 1, period 13. -/
def p913 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert913 : zipCycle p913 1 13 true (-1) = true := by decide +kernel
theorem never913 (m : Machine) (hm : compatible p913 m) : NeverHalts m :=
  zipCycle_sound p913 1 13 true (-1) (by decide) cert913 m hm
#print axioms never913


/-- Third-level first-hole refinement 914, 1RB---_1RC0LE_0RD---_1LD1RB_0LB0LB_------; entry 10, period 7. -/
def p914 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert914 : zipCycle p914 10 7 false (0) = true := by decide +kernel
theorem never914 (m : Machine) (hm : compatible p914 m) : NeverHalts m :=
  zipCycle_sound p914 10 7 false (0) (by decide) cert914 m hm
#print axioms never914


/-- Third-level first-hole refinement 915, 1RB---_1RC0LE_0RD---_1LD1RB_0RB0LB_------; entry 10, period 7. -/
def p915 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert915 : zipCycle p915 10 7 false (2) = true := by decide +kernel
theorem never915 (m : Machine) (hm : compatible p915 m) : NeverHalts m :=
  zipCycle_sound p915 10 7 false (2) (by decide) cert915 m hm
#print axioms never915


/-- Third-level first-hole refinement 916, 1RB---_1RC0LE_0RD---_1LD1RB_1RB0LB_------; entry 1, period 9. -/
def p916 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert916 : zipCycle p916 1 9 false (3) = true := by decide +kernel
theorem never916 (m : Machine) (hm : compatible p916 m) : NeverHalts m :=
  zipCycle_sound p916 1 9 false (3) (by decide) cert916 m hm
#print axioms never916


/-- Third-level first-hole refinement 917, 1RB---_1RC0LE_0RD---_1LD1RB_0LC0LB_------; entry 11, period 1. -/
def p917 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert917 : zipCycle p917 11 1 false (-1) = true := by decide +kernel
theorem never917 (m : Machine) (hm : compatible p917 m) : NeverHalts m :=
  zipCycle_sound p917 11 1 false (-1) (by decide) cert917 m hm
#print axioms never917


/-- Third-level first-hole refinement 918, 1RB---_1RC0LE_0RD---_1LD1RB_1LC0LB_------; entry 1, period 11. -/
def p918 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert918 : zipCycle p918 1 11 false (3) = true := by decide +kernel
theorem never918 (m : Machine) (hm : compatible p918 m) : NeverHalts m :=
  zipCycle_sound p918 1 11 false (3) (by decide) cert918 m hm
#print axioms never918


/-- Third-level first-hole refinement 919, 1RB---_1RC0LE_0RD---_1LD1RB_0RC0LB_------; entry 11, period 1. -/
def p919 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert919 : zipCycle p919 11 1 false (1) = true := by decide +kernel
theorem never919 (m : Machine) (hm : compatible p919 m) : NeverHalts m :=
  zipCycle_sound p919 11 1 false (1) (by decide) cert919 m hm
#print axioms never919


/-- Third-level first-hole refinement 920, 1RB---_1RC0LE_0RD---_1LD1RB_1RC0LB_------; entry 10, period 7. -/
def p920 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert920 : zipCycle p920 10 7 false (1) = true := by decide +kernel
theorem never920 (m : Machine) (hm : compatible p920 m) : NeverHalts m :=
  zipCycle_sound p920 10 7 false (1) (by decide) cert920 m hm
#print axioms never920


/-- Third-level first-hole refinement 921, 1RB---_1RC0LE_0RD---_1LD1RB_0LD0LB_------; entry 10, period 1. -/
def p921 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert921 : zipCycle p921 10 1 false (-2) = true := by decide +kernel
theorem never921 (m : Machine) (hm : compatible p921 m) : NeverHalts m :=
  zipCycle_sound p921 10 1 false (-2) (by decide) cert921 m hm
#print axioms never921


/-- Third-level first-hole refinement 922, 1RB---_1RC0LE_0RD---_1LD1RB_1LD0LB_------; entry 10, period 1. -/
def p922 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert922 : zipCycle p922 10 1 false (-2) = true := by decide +kernel
theorem never922 (m : Machine) (hm : compatible p922 m) : NeverHalts m :=
  zipCycle_sound p922 10 1 false (-2) (by decide) cert922 m hm
#print axioms never922


/-- Third-level first-hole refinement 923, 1RB---_1RC0LE_0RD---_1LD1RB_0RD0LB_------; entry 10, period 1. -/
def p923 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert923 : zipCycle p923 10 1 false (0) = true := by decide +kernel
theorem never923 (m : Machine) (hm : compatible p923 m) : NeverHalts m :=
  zipCycle_sound p923 10 1 false (0) (by decide) cert923 m hm
#print axioms never923


/-- Third-level first-hole refinement 924, 1RB---_1RC0LE_0RD---_1LD1RB_1RD0LB_------; entry 10, period 7. -/
def p924 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert924 : zipCycle p924 10 7 false (0) = true := by decide +kernel
theorem never924 (m : Machine) (hm : compatible p924 m) : NeverHalts m :=
  zipCycle_sound p924 10 7 false (0) (by decide) cert924 m hm
#print axioms never924


/-- Third-level first-hole refinement 925, 1RB---_1RC0LE_0RD---_1LD1RB_0LE0LB_------; entry 9, period 1. -/
def p925 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert925 : zipCycle p925 9 1 false (-1) = true := by decide +kernel
theorem never925 (m : Machine) (hm : compatible p925 m) : NeverHalts m :=
  zipCycle_sound p925 9 1 false (-1) (by decide) cert925 m hm
#print axioms never925


/-- Third-level first-hole refinement 926, 1RB---_1RC0LE_0RD---_1LD1RB_1LE0LB_------; entry 9, period 1. -/
def p926 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert926 : zipCycle p926 9 1 false (-1) = true := by decide +kernel
theorem never926 (m : Machine) (hm : compatible p926 m) : NeverHalts m :=
  zipCycle_sound p926 9 1 false (-1) (by decide) cert926 m hm
#print axioms never926


/-- Third-level first-hole refinement 927, 1RB---_1RC0LE_0RD---_1LD1RB_0RE0LB_------; entry 13, period 7. -/
def p927 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert927 : zipCycle p927 13 7 false (4) = true := by decide +kernel
theorem never927 (m : Machine) (hm : compatible p927 m) : NeverHalts m :=
  zipCycle_sound p927 13 7 false (4) (by decide) cert927 m hm
#print axioms never927


/-- Third-level first-hole refinement 928, 1RB---_1RC0LE_0RD---_1LD1RB_1RE0LB_------; entry 16, period 7. -/
def p928 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,1⟩)
  | _,_ => none
theorem cert928 : zipCycle p928 16 7 false (0) = true := by decide +kernel
theorem never928 (m : Machine) (hm : compatible p928 m) : NeverHalts m :=
  zipCycle_sound p928 16 7 false (0) (by decide) cert928 m hm
#print axioms never928


/-- Third-level first-hole refinement 929, 1RB---_1RC0LE_0RD---_1LD1RB_1RA1LB_------; entry 6, period 5. -/
def p929 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert929 : zipCycle p929 6 5 false (2) = true := by decide +kernel
theorem never929 (m : Machine) (hm : compatible p929 m) : NeverHalts m :=
  zipCycle_sound p929 6 5 false (2) (by decide) cert929 m hm
#print axioms never929


/-- Third-level first-hole refinement 930, 1RB---_1RC0LE_0RD---_1LD1RB_0LC1LB_------; entry 11, period 1. -/
def p930 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert930 : zipCycle p930 11 1 false (-1) = true := by decide +kernel
theorem never930 (m : Machine) (hm : compatible p930 m) : NeverHalts m :=
  zipCycle_sound p930 11 1 false (-1) (by decide) cert930 m hm
#print axioms never930


/-- Third-level first-hole refinement 931, 1RB---_1RC0LE_0RD---_1LD1RB_0LD1LB_------; entry 10, period 1. -/
def p931 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert931 : zipCycle p931 10 1 false (-2) = true := by decide +kernel
theorem never931 (m : Machine) (hm : compatible p931 m) : NeverHalts m :=
  zipCycle_sound p931 10 1 false (-2) (by decide) cert931 m hm
#print axioms never931


/-- Third-level first-hole refinement 932, 1RB---_1RC0LE_0RD---_1LD1RB_1LD1LB_------; entry 10, period 1. -/
def p932 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert932 : zipCycle p932 10 1 false (-2) = true := by decide +kernel
theorem never932 (m : Machine) (hm : compatible p932 m) : NeverHalts m :=
  zipCycle_sound p932 10 1 false (-2) (by decide) cert932 m hm
#print axioms never932


/-- Third-level first-hole refinement 933, 1RB---_1RC0LE_0RD---_1LD1RB_0RD1LB_------; entry 10, period 1. -/
def p933 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert933 : zipCycle p933 10 1 false (0) = true := by decide +kernel
theorem never933 (m : Machine) (hm : compatible p933 m) : NeverHalts m :=
  zipCycle_sound p933 10 1 false (0) (by decide) cert933 m hm
#print axioms never933


/-- Third-level first-hole refinement 934, 1RB---_1RC0LE_0RD---_1LD1RB_0LE1LB_------; entry 9, period 1. -/
def p934 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert934 : zipCycle p934 9 1 false (-1) = true := by decide +kernel
theorem never934 (m : Machine) (hm : compatible p934 m) : NeverHalts m :=
  zipCycle_sound p934 9 1 false (-1) (by decide) cert934 m hm
#print axioms never934


/-- Third-level first-hole refinement 935, 1RB---_1RC0LE_0RD---_1LD1RB_1LE1LB_------; entry 9, period 1. -/
def p935 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert935 : zipCycle p935 9 1 false (-1) = true := by decide +kernel
theorem never935 (m : Machine) (hm : compatible p935 m) : NeverHalts m :=
  zipCycle_sound p935 9 1 false (-1) (by decide) cert935 m hm
#print axioms never935


/-- Third-level first-hole refinement 936, 1RB---_1RC0LE_0RD0RA_1LD1RB_---0RB_------; entry 0, period 10. -/
def p936 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert936 : zipCycle p936 0 10 true (0) = true := by decide +kernel
theorem never936 (m : Machine) (hm : compatible p936 m) : NeverHalts m :=
  zipCycle_sound p936 0 10 true (0) (by decide) cert936 m hm
#print axioms never936


/-- Third-level first-hole refinement 937, 1RB---_1RC0LE_0RD1RA_1LD1RB_---0RB_------; entry 0, period 10. -/
def p937 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert937 : zipCycle p937 0 10 true (0) = true := by decide +kernel
theorem never937 (m : Machine) (hm : compatible p937 m) : NeverHalts m :=
  zipCycle_sound p937 0 10 true (0) (by decide) cert937 m hm
#print axioms never937


/-- Third-level first-hole refinement 938, 1RB---_1RC0LE_0RD0RB_1LD1RB_---0RB_------; entry 1, period 9. -/
def p938 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert938 : zipCycle p938 1 9 true (1) = true := by decide +kernel
theorem never938 (m : Machine) (hm : compatible p938 m) : NeverHalts m :=
  zipCycle_sound p938 1 9 true (1) (by decide) cert938 m hm
#print axioms never938


/-- Third-level first-hole refinement 939, 1RB---_1RC0LE_0RD1RB_1LD1RB_---0RB_------; entry 1, period 9. -/
def p939 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert939 : zipCycle p939 1 9 true (1) = true := by decide +kernel
theorem never939 (m : Machine) (hm : compatible p939 m) : NeverHalts m :=
  zipCycle_sound p939 1 9 true (1) (by decide) cert939 m hm
#print axioms never939


/-- Third-level first-hole refinement 940, 1RB---_1RC0LE_0RD0LC_1LD1RB_---0RB_------; entry 21, period 1. -/
def p940 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert940 : zipCycle p940 21 1 false (1) = true := by decide +kernel
theorem never940 (m : Machine) (hm : compatible p940 m) : NeverHalts m :=
  zipCycle_sound p940 21 1 false (1) (by decide) cert940 m hm
#print axioms never940


/-- Third-level first-hole refinement 941, 1RB---_1RC0LE_0RD1LC_1LD1RB_---0RB_------; entry 1, period 14. -/
def p941 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert941 : zipCycle p941 1 14 true (1) = true := by decide +kernel
theorem never941 (m : Machine) (hm : compatible p941 m) : NeverHalts m :=
  zipCycle_sound p941 1 14 true (1) (by decide) cert941 m hm
#print axioms never941


/-- Third-level first-hole refinement 942, 1RB---_1RC0LE_0RD1RC_1LD1RB_---0RB_------; entry 2, period 8. -/
def p942 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert942 : zipCycle p942 2 8 true (1) = true := by decide +kernel
theorem never942 (m : Machine) (hm : compatible p942 m) : NeverHalts m :=
  zipCycle_sound p942 2 8 true (1) (by decide) cert942 m hm
#print axioms never942


/-- Third-level first-hole refinement 943, 1RB---_1RC0LE_0RD0LD_1LD1RB_---0RB_------; entry 1, period 10. -/
def p943 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert943 : zipCycle p943 1 10 true (1) = true := by decide +kernel
theorem never943 (m : Machine) (hm : compatible p943 m) : NeverHalts m :=
  zipCycle_sound p943 1 10 true (1) (by decide) cert943 m hm
#print axioms never943


/-- Third-level first-hole refinement 944, 1RB---_1RC0LE_0RD1LD_1LD1RB_---0RB_------; entry 1, period 12. -/
def p944 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert944 : zipCycle p944 1 12 true (1) = true := by decide +kernel
theorem never944 (m : Machine) (hm : compatible p944 m) : NeverHalts m :=
  zipCycle_sound p944 1 12 true (1) (by decide) cert944 m hm
#print axioms never944


/-- Third-level first-hole refinement 945, 1RB---_1RC0LE_0RD0RD_1LD1RB_---0RB_------; entry 3, period 7. -/
def p945 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert945 : zipCycle p945 3 7 true (1) = true := by decide +kernel
theorem never945 (m : Machine) (hm : compatible p945 m) : NeverHalts m :=
  zipCycle_sound p945 3 7 true (1) (by decide) cert945 m hm
#print axioms never945


/-- Third-level first-hole refinement 946, 1RB---_1RC0LE_0RD1RD_1LD1RB_---0RB_------; entry 1, period 13. -/
def p946 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert946 : zipCycle p946 1 13 true (1) = true := by decide +kernel
theorem never946 (m : Machine) (hm : compatible p946 m) : NeverHalts m :=
  zipCycle_sound p946 1 13 true (1) (by decide) cert946 m hm
#print axioms never946


/-- Third-level first-hole refinement 947, 1RB---_1RC0LE_0RD0LE_1LD1RB_---0RB_------; entry 1, period 10. -/
def p947 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,1⟩)
  | _,_ => none
theorem cert947 : zipCycle p947 1 10 true (1) = true := by decide +kernel
theorem never947 (m : Machine) (hm : compatible p947 m) : NeverHalts m :=
  zipCycle_sound p947 1 10 true (1) (by decide) cert947 m hm
#print axioms never947


/-- Third-level first-hole refinement 948, 1RB---_1RC0LE_0RD0RA_1LD1RB_---1RB_------; entry 0, period 10. -/
def p948 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert948 : zipCycle p948 0 10 true (0) = true := by decide +kernel
theorem never948 (m : Machine) (hm : compatible p948 m) : NeverHalts m :=
  zipCycle_sound p948 0 10 true (0) (by decide) cert948 m hm
#print axioms never948


/-- Third-level first-hole refinement 949, 1RB---_1RC0LE_0RD1RA_1LD1RB_---1RB_------; entry 0, period 10. -/
def p949 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert949 : zipCycle p949 0 10 true (0) = true := by decide +kernel
theorem never949 (m : Machine) (hm : compatible p949 m) : NeverHalts m :=
  zipCycle_sound p949 0 10 true (0) (by decide) cert949 m hm
#print axioms never949


/-- Third-level first-hole refinement 950, 1RB---_1RC0LE_0RD0LB_1LD1RB_---1RB_------; entry 1, period 11. -/
def p950 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert950 : zipCycle p950 1 11 true (1) = true := by decide +kernel
theorem never950 (m : Machine) (hm : compatible p950 m) : NeverHalts m :=
  zipCycle_sound p950 1 11 true (1) (by decide) cert950 m hm
#print axioms never950


/-- Third-level first-hole refinement 951, 1RB---_1RC0LE_0RD1LB_1LD1RB_---1RB_------; entry 6, period 4. -/
def p951 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert951 : zipCycle p951 6 4 true (1) = true := by decide +kernel
theorem never951 (m : Machine) (hm : compatible p951 m) : NeverHalts m :=
  zipCycle_sound p951 6 4 true (1) (by decide) cert951 m hm
#print axioms never951


/-- Third-level first-hole refinement 952, 1RB---_1RC0LE_0RD0RB_1LD1RB_---1RB_------; entry 1, period 9. -/
def p952 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert952 : zipCycle p952 1 9 true (1) = true := by decide +kernel
theorem never952 (m : Machine) (hm : compatible p952 m) : NeverHalts m :=
  zipCycle_sound p952 1 9 true (1) (by decide) cert952 m hm
#print axioms never952


/-- Third-level first-hole refinement 953, 1RB---_1RC0LE_0RD1RB_1LD1RB_---1RB_------; entry 1, period 9. -/
def p953 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert953 : zipCycle p953 1 9 true (1) = true := by decide +kernel
theorem never953 (m : Machine) (hm : compatible p953 m) : NeverHalts m :=
  zipCycle_sound p953 1 9 true (1) (by decide) cert953 m hm
#print axioms never953


/-- Third-level first-hole refinement 954, 1RB---_1RC0LE_0RD0LC_1LD1RB_---1RB_------; entry 14, period 1. -/
def p954 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert954 : zipCycle p954 14 1 false (0) = true := by decide +kernel
theorem never954 (m : Machine) (hm : compatible p954 m) : NeverHalts m :=
  zipCycle_sound p954 14 1 false (0) (by decide) cert954 m hm
#print axioms never954


/-- Third-level first-hole refinement 955, 1RB---_1RC0LE_0RD1LC_1LD1RB_---1RB_------; entry 10, period 8. -/
def p955 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert955 : zipCycle p955 10 8 true (-1) = true := by decide +kernel
theorem never955 (m : Machine) (hm : compatible p955 m) : NeverHalts m :=
  zipCycle_sound p955 10 8 true (-1) (by decide) cert955 m hm
#print axioms never955


/-- Third-level first-hole refinement 956, 1RB---_1RC0LE_0RD1RC_1LD1RB_---1RB_------; entry 2, period 8. -/
def p956 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert956 : zipCycle p956 2 8 true (1) = true := by decide +kernel
theorem never956 (m : Machine) (hm : compatible p956 m) : NeverHalts m :=
  zipCycle_sound p956 2 8 true (1) (by decide) cert956 m hm
#print axioms never956


/-- Third-level first-hole refinement 957, 1RB---_1RC0LE_0RD0LD_1LD1RB_---1RB_------; entry 1, period 10. -/
def p957 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert957 : zipCycle p957 1 10 true (1) = true := by decide +kernel
theorem never957 (m : Machine) (hm : compatible p957 m) : NeverHalts m :=
  zipCycle_sound p957 1 10 true (1) (by decide) cert957 m hm
#print axioms never957


/-- Third-level first-hole refinement 958, 1RB---_1RC0LE_0RD1LD_1LD1RB_---1RB_------; entry 1, period 12. -/
def p958 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert958 : zipCycle p958 1 12 true (1) = true := by decide +kernel
theorem never958 (m : Machine) (hm : compatible p958 m) : NeverHalts m :=
  zipCycle_sound p958 1 12 true (1) (by decide) cert958 m hm
#print axioms never958


/-- Third-level first-hole refinement 959, 1RB---_1RC0LE_0RD0RD_1LD1RB_---1RB_------; entry 3, period 7. -/
def p959 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert959 : zipCycle p959 3 7 true (1) = true := by decide +kernel
theorem never959 (m : Machine) (hm : compatible p959 m) : NeverHalts m :=
  zipCycle_sound p959 3 7 true (1) (by decide) cert959 m hm
#print axioms never959


/-- Third-level first-hole refinement 960, 1RB---_1RC0LE_0RD1RD_1LD1RB_---1RB_------; entry 1, period 13. -/
def p960 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert960 : zipCycle p960 1 13 true (1) = true := by decide +kernel
theorem never960 (m : Machine) (hm : compatible p960 m) : NeverHalts m :=
  zipCycle_sound p960 1 13 true (1) (by decide) cert960 m hm
#print axioms never960


/-- Third-level first-hole refinement 961, 1RB---_1RC0LE_0RD0LE_1LD1RB_---1RB_------; entry 1, period 10. -/
def p961 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert961 : zipCycle p961 1 10 true (1) = true := by decide +kernel
theorem never961 (m : Machine) (hm : compatible p961 m) : NeverHalts m :=
  zipCycle_sound p961 1 10 true (1) (by decide) cert961 m hm
#print axioms never961


/-- Third-level first-hole refinement 962, 1RB---_1RC0LE_0RD1LE_1LD1RB_---1RB_------; entry 1, period 12. -/
def p962 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,1⟩)
  | _,_ => none
theorem cert962 : zipCycle p962 1 12 true (1) = true := by decide +kernel
theorem never962 (m : Machine) (hm : compatible p962 m) : NeverHalts m :=
  zipCycle_sound p962 1 12 true (1) (by decide) cert962 m hm
#print axioms never962


/-- Third-level first-hole refinement 963, 1RB---_1RC0LE_0RD0LA_1LD1RB_---0LC_------; entry 0, period 9. -/
def p963 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert963 : zipCycle p963 0 9 false (3) = true := by decide +kernel
theorem never963 (m : Machine) (hm : compatible p963 m) : NeverHalts m :=
  zipCycle_sound p963 0 9 false (3) (by decide) cert963 m hm
#print axioms never963


/-- Third-level first-hole refinement 964, 1RB---_1RC0LE_0RD1LA_1LD1RB_---0LC_------; entry 13, period 1. -/
def p964 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert964 : zipCycle p964 13 1 false (-1) = true := by decide +kernel
theorem never964 (m : Machine) (hm : compatible p964 m) : NeverHalts m :=
  zipCycle_sound p964 13 1 false (-1) (by decide) cert964 m hm
#print axioms never964


/-- Third-level first-hole refinement 965, 1RB---_1RC0LE_0RD0RA_1LD1RB_---0LC_------; entry 0, period 12. -/
def p965 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert965 : zipCycle p965 0 12 true (0) = true := by decide +kernel
theorem never965 (m : Machine) (hm : compatible p965 m) : NeverHalts m :=
  zipCycle_sound p965 0 12 true (0) (by decide) cert965 m hm
#print axioms never965


/-- Third-level first-hole refinement 966, 1RB---_1RC0LE_0RD1RA_1LD1RB_---0LC_------; entry 0, period 12. -/
def p966 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert966 : zipCycle p966 0 12 true (0) = true := by decide +kernel
theorem never966 (m : Machine) (hm : compatible p966 m) : NeverHalts m :=
  zipCycle_sound p966 0 12 true (0) (by decide) cert966 m hm
#print axioms never966


/-- Third-level first-hole refinement 967, 1RB---_1RC0LE_0RD0LB_1LD1RB_---0LC_------; entry 17, period 1. -/
def p967 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert967 : zipCycle p967 17 1 false (-1) = true := by decide +kernel
theorem never967 (m : Machine) (hm : compatible p967 m) : NeverHalts m :=
  zipCycle_sound p967 17 1 false (-1) (by decide) cert967 m hm
#print axioms never967


/-- Third-level first-hole refinement 968, 1RB---_1RC0LE_0RD0RB_1LD1RB_---0LC_------; entry 1, period 11. -/
def p968 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert968 : zipCycle p968 1 11 true (0) = true := by decide +kernel
theorem never968 (m : Machine) (hm : compatible p968 m) : NeverHalts m :=
  zipCycle_sound p968 1 11 true (0) (by decide) cert968 m hm
#print axioms never968


/-- Third-level first-hole refinement 969, 1RB---_1RC0LE_0RD1RB_1LD1RB_---0LC_------; entry 1, period 11. -/
def p969 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert969 : zipCycle p969 1 11 true (0) = true := by decide +kernel
theorem never969 (m : Machine) (hm : compatible p969 m) : NeverHalts m :=
  zipCycle_sound p969 1 11 true (0) (by decide) cert969 m hm
#print axioms never969


/-- Third-level first-hole refinement 970, 1RB---_1RC0LE_0RD0LC_1LD1RB_---0LC_------; entry 10, period 1. -/
def p970 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert970 : zipCycle p970 10 1 false (0) = true := by decide +kernel
theorem never970 (m : Machine) (hm : compatible p970 m) : NeverHalts m :=
  zipCycle_sound p970 10 1 false (0) (by decide) cert970 m hm
#print axioms never970


/-- Third-level first-hole refinement 971, 1RB---_1RC0LE_0RD1LC_1LD1RB_---0LC_------; entry 1, period 13. -/
def p971 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert971 : zipCycle p971 1 13 true (-1) = true := by decide +kernel
theorem never971 (m : Machine) (hm : compatible p971 m) : NeverHalts m :=
  zipCycle_sound p971 1 13 true (-1) (by decide) cert971 m hm
#print axioms never971


/-- Third-level first-hole refinement 972, 1RB---_1RC0LE_0RD0RC_1LD1RB_---0LC_------; entry 10, period 1. -/
def p972 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert972 : zipCycle p972 10 1 false (2) = true := by decide +kernel
theorem never972 (m : Machine) (hm : compatible p972 m) : NeverHalts m :=
  zipCycle_sound p972 10 1 false (2) (by decide) cert972 m hm
#print axioms never972


/-- Third-level first-hole refinement 973, 1RB---_1RC0LE_0RD1RC_1LD1RB_---0LC_------; entry 16, period 1. -/
def p973 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert973 : zipCycle p973 16 1 false (0) = true := by decide +kernel
theorem never973 (m : Machine) (hm : compatible p973 m) : NeverHalts m :=
  zipCycle_sound p973 16 1 false (0) (by decide) cert973 m hm
#print axioms never973


/-- Third-level first-hole refinement 974, 1RB---_1RC0LE_0RD0LD_1LD1RB_---0LC_------; entry 9, period 1. -/
def p974 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert974 : zipCycle p974 9 1 false (-1) = true := by decide +kernel
theorem never974 (m : Machine) (hm : compatible p974 m) : NeverHalts m :=
  zipCycle_sound p974 9 1 false (-1) (by decide) cert974 m hm
#print axioms never974


/-- Third-level first-hole refinement 975, 1RB---_1RC0LE_0RD1LD_1LD1RB_---0LC_------; entry 9, period 1. -/
def p975 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert975 : zipCycle p975 9 1 false (-1) = true := by decide +kernel
theorem never975 (m : Machine) (hm : compatible p975 m) : NeverHalts m :=
  zipCycle_sound p975 9 1 false (-1) (by decide) cert975 m hm
#print axioms never975


/-- Third-level first-hole refinement 976, 1RB---_1RC0LE_0RD0RD_1LD1RB_---0LC_------; entry 9, period 1. -/
def p976 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert976 : zipCycle p976 9 1 false (1) = true := by decide +kernel
theorem never976 (m : Machine) (hm : compatible p976 m) : NeverHalts m :=
  zipCycle_sound p976 9 1 false (1) (by decide) cert976 m hm
#print axioms never976


/-- Third-level first-hole refinement 977, 1RB---_1RC0LE_0RD1RD_1LD1RB_---0LC_------; entry 14, period 1. -/
def p977 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,2⟩)
  | _,_ => none
theorem cert977 : zipCycle p977 14 1 false (0) = true := by decide +kernel
theorem never977 (m : Machine) (hm : compatible p977 m) : NeverHalts m :=
  zipCycle_sound p977 14 1 false (0) (by decide) cert977 m hm
#print axioms never977


/-- Third-level first-hole refinement 978, 1RB---_1RC0LE_0RD0LB_1LD1RB_---1LC_------; entry 1, period 17. -/
def p978 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert978 : zipCycle p978 1 17 true (-1) = true := by decide +kernel
theorem never978 (m : Machine) (hm : compatible p978 m) : NeverHalts m :=
  zipCycle_sound p978 1 17 true (-1) (by decide) cert978 m hm
#print axioms never978


/-- Third-level first-hole refinement 979, 1RB---_1RC0LE_0RD1RB_1LD1RB_---1LC_------; entry 1, period 15. -/
def p979 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert979 : zipCycle p979 1 15 true (-1) = true := by decide +kernel
theorem never979 (m : Machine) (hm : compatible p979 m) : NeverHalts m :=
  zipCycle_sound p979 1 15 true (-1) (by decide) cert979 m hm
#print axioms never979


/-- Third-level first-hole refinement 980, 1RB---_1RC0LE_0RD0LC_1LD1RB_---1LC_------; entry 10, period 1. -/
def p980 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert980 : zipCycle p980 10 1 false (0) = true := by decide +kernel
theorem never980 (m : Machine) (hm : compatible p980 m) : NeverHalts m :=
  zipCycle_sound p980 10 1 false (0) (by decide) cert980 m hm
#print axioms never980


/-- Third-level first-hole refinement 981, 1RB---_1RC0LE_0RD1LC_1LD1RB_---1LC_------; entry 1, period 17. -/
def p981 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert981 : zipCycle p981 1 17 true (-1) = true := by decide +kernel
theorem never981 (m : Machine) (hm : compatible p981 m) : NeverHalts m :=
  zipCycle_sound p981 1 17 true (-1) (by decide) cert981 m hm
#print axioms never981


/-- Third-level first-hole refinement 982, 1RB---_1RC0LE_0RD0RC_1LD1RB_---1LC_------; entry 1, period 11. -/
def p982 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert982 : zipCycle p982 1 11 true (0) = true := by decide +kernel
theorem never982 (m : Machine) (hm : compatible p982 m) : NeverHalts m :=
  zipCycle_sound p982 1 11 true (0) (by decide) cert982 m hm
#print axioms never982


/-- Third-level first-hole refinement 983, 1RB---_1RC0LE_0RD1RC_1LD1RB_---1LC_------; entry 1, period 11. -/
def p983 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert983 : zipCycle p983 1 11 true (0) = true := by decide +kernel
theorem never983 (m : Machine) (hm : compatible p983 m) : NeverHalts m :=
  zipCycle_sound p983 1 11 true (0) (by decide) cert983 m hm
#print axioms never983


/-- Third-level first-hole refinement 984, 1RB---_1RC0LE_0RD0LD_1LD1RB_---1LC_------; entry 9, period 1. -/
def p984 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert984 : zipCycle p984 9 1 false (-1) = true := by decide +kernel
theorem never984 (m : Machine) (hm : compatible p984 m) : NeverHalts m :=
  zipCycle_sound p984 9 1 false (-1) (by decide) cert984 m hm
#print axioms never984


/-- Third-level first-hole refinement 985, 1RB---_1RC0LE_0RD1LD_1LD1RB_---1LC_------; entry 9, period 1. -/
def p985 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert985 : zipCycle p985 9 1 false (-1) = true := by decide +kernel
theorem never985 (m : Machine) (hm : compatible p985 m) : NeverHalts m :=
  zipCycle_sound p985 9 1 false (-1) (by decide) cert985 m hm
#print axioms never985


/-- Third-level first-hole refinement 986, 1RB---_1RC0LE_0RD0RD_1LD1RB_---1LC_------; entry 3, period 9. -/
def p986 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert986 : zipCycle p986 3 9 true (0) = true := by decide +kernel
theorem never986 (m : Machine) (hm : compatible p986 m) : NeverHalts m :=
  zipCycle_sound p986 3 9 true (0) (by decide) cert986 m hm
#print axioms never986


/-- Third-level first-hole refinement 987, 1RB---_1RC0LE_0RD1RD_1LD1RB_---1LC_------; entry 1, period 17. -/
def p987 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert987 : zipCycle p987 1 17 true (0) = true := by decide +kernel
theorem never987 (m : Machine) (hm : compatible p987 m) : NeverHalts m :=
  zipCycle_sound p987 1 17 true (0) (by decide) cert987 m hm
#print axioms never987


/-- Third-level first-hole refinement 988, 1RB---_1RC0LE_0RD1RE_1LD1RB_---1LC_------; entry 7, period 2. -/
def p988 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,2⟩)
  | _,_ => none
theorem cert988 : zipCycle p988 7 2 true (0) = true := by decide +kernel
theorem never988 (m : Machine) (hm : compatible p988 m) : NeverHalts m :=
  zipCycle_sound p988 7 2 true (0) (by decide) cert988 m hm
#print axioms never988


/-- Third-level first-hole refinement 989, 1RB---_1RC0LE_0RD---_1LD1RB_0LA0LE_------; entry 0, period 10. -/
def p989 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert989 : zipCycle p989 0 10 false (3) = true := by decide +kernel
theorem never989 (m : Machine) (hm : compatible p989 m) : NeverHalts m :=
  zipCycle_sound p989 0 10 false (3) (by decide) cert989 m hm
#print axioms never989


/-- Third-level first-hole refinement 990, 1RB---_1RC0LE_0RD---_1LD1RB_1LA0LE_------; entry 8, period 4. -/
def p990 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert990 : zipCycle p990 8 4 false (0) = true := by decide +kernel
theorem never990 (m : Machine) (hm : compatible p990 m) : NeverHalts m :=
  zipCycle_sound p990 8 4 false (0) (by decide) cert990 m hm
#print axioms never990


/-- Third-level first-hole refinement 991, 1RB---_1RC0LE_0RD---_1LD1RB_0RA0LE_------; entry 1, period 13. -/
def p991 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert991 : zipCycle p991 1 13 true (-1) = true := by decide +kernel
theorem never991 (m : Machine) (hm : compatible p991 m) : NeverHalts m :=
  zipCycle_sound p991 1 13 true (-1) (by decide) cert991 m hm
#print axioms never991


/-- Third-level first-hole refinement 992, 1RB---_1RC0LE_0RD---_1LD1RB_1RA0LE_------; entry 1, period 13. -/
def p992 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert992 : zipCycle p992 1 13 true (-1) = true := by decide +kernel
theorem never992 (m : Machine) (hm : compatible p992 m) : NeverHalts m :=
  zipCycle_sound p992 1 13 true (-1) (by decide) cert992 m hm
#print axioms never992


/-- Third-level first-hole refinement 993, 1RB---_1RC0LE_0RD---_1LD1RB_0LB0LE_------; entry 8, period 8. -/
def p993 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert993 : zipCycle p993 8 8 false (0) = true := by decide +kernel
theorem never993 (m : Machine) (hm : compatible p993 m) : NeverHalts m :=
  zipCycle_sound p993 8 8 false (0) (by decide) cert993 m hm
#print axioms never993


/-- Third-level first-hole refinement 994, 1RB---_1RC0LE_0RD---_1LD1RB_1RB0LE_------; entry 1, period 9. -/
def p994 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert994 : zipCycle p994 1 9 false (3) = true := by decide +kernel
theorem never994 (m : Machine) (hm : compatible p994 m) : NeverHalts m :=
  zipCycle_sound p994 1 9 false (3) (by decide) cert994 m hm
#print axioms never994


/-- Third-level first-hole refinement 995, 1RB---_1RC0LE_0RD---_1LD1RB_0LC0LE_------; entry 11, period 1. -/
def p995 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert995 : zipCycle p995 11 1 false (-1) = true := by decide +kernel
theorem never995 (m : Machine) (hm : compatible p995 m) : NeverHalts m :=
  zipCycle_sound p995 11 1 false (-1) (by decide) cert995 m hm
#print axioms never995


/-- Third-level first-hole refinement 996, 1RB---_1RC0LE_0RD---_1LD1RB_1LC0LE_------; entry 1, period 11. -/
def p996 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert996 : zipCycle p996 1 11 false (3) = true := by decide +kernel
theorem never996 (m : Machine) (hm : compatible p996 m) : NeverHalts m :=
  zipCycle_sound p996 1 11 false (3) (by decide) cert996 m hm
#print axioms never996


/-- Third-level first-hole refinement 997, 1RB---_1RC0LE_0RD---_1LD1RB_0RC0LE_------; entry 11, period 1. -/
def p997 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert997 : zipCycle p997 11 1 false (1) = true := by decide +kernel
theorem never997 (m : Machine) (hm : compatible p997 m) : NeverHalts m :=
  zipCycle_sound p997 11 1 false (1) (by decide) cert997 m hm
#print axioms never997


/-- Third-level first-hole refinement 998, 1RB---_1RC0LE_0RD---_1LD1RB_1RC0LE_------; entry 8, period 7. -/
def p998 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert998 : zipCycle p998 8 7 false (1) = true := by decide +kernel
theorem never998 (m : Machine) (hm : compatible p998 m) : NeverHalts m :=
  zipCycle_sound p998 8 7 false (1) (by decide) cert998 m hm
#print axioms never998


/-- Third-level first-hole refinement 999, 1RB---_1RC0LE_0RD---_1LD1RB_0LD0LE_------; entry 10, period 1. -/
def p999 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,false,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert999 : zipCycle p999 10 1 false (-2) = true := by decide +kernel
theorem never999 (m : Machine) (hm : compatible p999 m) : NeverHalts m :=
  zipCycle_sound p999 10 1 false (-2) (by decide) cert999 m hm
#print axioms never999

end BB6.Agent24Raw45D3_09
