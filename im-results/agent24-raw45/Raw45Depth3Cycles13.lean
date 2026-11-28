import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45D3_13
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- Third-level first-hole refinement 1300, 1RB---_1RC0RE_0RD---_1LD1RB_1RE1LA_------; entry 10, period 1. -/
def p1300 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,0⟩)
  | _,_ => none
theorem cert1300 : zipCycle p1300 10 1 true (4) = true := by decide +kernel
theorem never1300 (m : Machine) (hm : compatible p1300 m) : NeverHalts m :=
  zipCycle_sound p1300 10 1 true (4) (by decide) cert1300 m hm
#print axioms never1300


/-- Third-level first-hole refinement 1301, 1RB---_1RC0RE_0RD0RA_1LD1RB_---1LB_------; entry 0, period 10. -/
def p1301 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1301 : zipCycle p1301 0 10 true (0) = true := by decide +kernel
theorem never1301 (m : Machine) (hm : compatible p1301 m) : NeverHalts m :=
  zipCycle_sound p1301 0 10 true (0) (by decide) cert1301 m hm
#print axioms never1301


/-- Third-level first-hole refinement 1302, 1RB---_1RC0RE_0RD1RA_1LD1RB_---1LB_------; entry 0, period 10. -/
def p1302 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1302 : zipCycle p1302 0 10 true (0) = true := by decide +kernel
theorem never1302 (m : Machine) (hm : compatible p1302 m) : NeverHalts m :=
  zipCycle_sound p1302 0 10 true (0) (by decide) cert1302 m hm
#print axioms never1302


/-- Third-level first-hole refinement 1303, 1RB---_1RC0RE_0RD1LB_1LD1RB_---1LB_------; entry 6, period 4. -/
def p1303 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1303 : zipCycle p1303 6 4 true (2) = true := by decide +kernel
theorem never1303 (m : Machine) (hm : compatible p1303 m) : NeverHalts m :=
  zipCycle_sound p1303 6 4 true (2) (by decide) cert1303 m hm
#print axioms never1303


/-- Third-level first-hole refinement 1304, 1RB---_1RC0RE_0RD0RB_1LD1RB_---1LB_------; entry 1, period 9. -/
def p1304 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1304 : zipCycle p1304 1 9 true (1) = true := by decide +kernel
theorem never1304 (m : Machine) (hm : compatible p1304 m) : NeverHalts m :=
  zipCycle_sound p1304 1 9 true (1) (by decide) cert1304 m hm
#print axioms never1304


/-- Third-level first-hole refinement 1305, 1RB---_1RC0RE_0RD1RB_1LD1RB_---1LB_------; entry 1, period 9. -/
def p1305 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1305 : zipCycle p1305 1 9 true (1) = true := by decide +kernel
theorem never1305 (m : Machine) (hm : compatible p1305 m) : NeverHalts m :=
  zipCycle_sound p1305 1 9 true (1) (by decide) cert1305 m hm
#print axioms never1305


/-- Third-level first-hole refinement 1306, 1RB---_1RC0RE_0RD0LC_1LD1RB_---1LB_------; entry 14, period 1. -/
def p1306 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1306 : zipCycle p1306 14 1 false (0) = true := by decide +kernel
theorem never1306 (m : Machine) (hm : compatible p1306 m) : NeverHalts m :=
  zipCycle_sound p1306 14 1 false (0) (by decide) cert1306 m hm
#print axioms never1306


/-- Third-level first-hole refinement 1307, 1RB---_1RC0RE_0RD1LC_1LD1RB_---1LB_------; entry 10, period 8. -/
def p1307 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1307 : zipCycle p1307 10 8 true (-1) = true := by decide +kernel
theorem never1307 (m : Machine) (hm : compatible p1307 m) : NeverHalts m :=
  zipCycle_sound p1307 10 8 true (-1) (by decide) cert1307 m hm
#print axioms never1307


/-- Third-level first-hole refinement 1308, 1RB---_1RC0RE_0RD1RC_1LD1RB_---1LB_------; entry 2, period 8. -/
def p1308 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1308 : zipCycle p1308 2 8 true (1) = true := by decide +kernel
theorem never1308 (m : Machine) (hm : compatible p1308 m) : NeverHalts m :=
  zipCycle_sound p1308 2 8 true (1) (by decide) cert1308 m hm
#print axioms never1308


/-- Third-level first-hole refinement 1309, 1RB---_1RC0RE_0RD0LD_1LD1RB_---1LB_------; entry 1, period 10. -/
def p1309 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1309 : zipCycle p1309 1 10 true (1) = true := by decide +kernel
theorem never1309 (m : Machine) (hm : compatible p1309 m) : NeverHalts m :=
  zipCycle_sound p1309 1 10 true (1) (by decide) cert1309 m hm
#print axioms never1309


/-- Third-level first-hole refinement 1310, 1RB---_1RC0RE_0RD0RD_1LD1RB_---1LB_------; entry 3, period 7. -/
def p1310 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1310 : zipCycle p1310 3 7 true (1) = true := by decide +kernel
theorem never1310 (m : Machine) (hm : compatible p1310 m) : NeverHalts m :=
  zipCycle_sound p1310 3 7 true (1) (by decide) cert1310 m hm
#print axioms never1310


/-- Third-level first-hole refinement 1311, 1RB---_1RC0RE_0RD0LE_1LD1RB_---1LB_------; entry 17, period 3. -/
def p1311 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1311 : zipCycle p1311 17 3 false (1) = true := by decide +kernel
theorem never1311 (m : Machine) (hm : compatible p1311 m) : NeverHalts m :=
  zipCycle_sound p1311 17 3 false (1) (by decide) cert1311 m hm
#print axioms never1311


/-- Third-level first-hole refinement 1312, 1RB---_1RC0RE_0RD1LE_1LD1RB_---1LB_------; entry 17, period 3. -/
def p1312 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,4⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,1⟩)
  | _,_ => none
theorem cert1312 : zipCycle p1312 17 3 false (1) = true := by decide +kernel
theorem never1312 (m : Machine) (hm : compatible p1312 m) : NeverHalts m :=
  zipCycle_sound p1312 17 3 false (1) (by decide) cert1312 m hm
#print axioms never1312


/-- Third-level first-hole refinement 1313, 1RB---_1RC0RE_0RD1LA_1LD1RB_---0RC_------; entry 6, period 12. -/
def p1313 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1313 : zipCycle p1313 6 12 true (1) = true := by decide +kernel
theorem never1313 (m : Machine) (hm : compatible p1313 m) : NeverHalts m :=
  zipCycle_sound p1313 6 12 true (1) (by decide) cert1313 m hm
#print axioms never1313


/-- Third-level first-hole refinement 1314, 1RB---_1RC0RE_0RD0LB_1LD1RB_---0RC_------; entry 1, period 19. -/
def p1314 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1314 : zipCycle p1314 1 19 true (1) = true := by decide +kernel
theorem never1314 (m : Machine) (hm : compatible p1314 m) : NeverHalts m :=
  zipCycle_sound p1314 1 19 true (1) (by decide) cert1314 m hm
#print axioms never1314


/-- Third-level first-hole refinement 1315, 1RB---_1RC0RE_0RD0LC_1LD1RB_---0RC_------; entry 10, period 8. -/
def p1315 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1315 : zipCycle p1315 10 8 true (1) = true := by decide +kernel
theorem never1315 (m : Machine) (hm : compatible p1315 m) : NeverHalts m :=
  zipCycle_sound p1315 10 8 true (1) (by decide) cert1315 m hm
#print axioms never1315


/-- Third-level first-hole refinement 1316, 1RB---_1RC0RE_0RD1RC_1LD1RB_---0RC_------; entry 2, period 16. -/
def p1316 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1316 : zipCycle p1316 2 16 true (1) = true := by decide +kernel
theorem never1316 (m : Machine) (hm : compatible p1316 m) : NeverHalts m :=
  zipCycle_sound p1316 2 16 true (1) (by decide) cert1316 m hm
#print axioms never1316


/-- Third-level first-hole refinement 1317, 1RB---_1RC0RE_0RD0LD_1LD1RB_---0RC_------; entry 1, period 23. -/
def p1317 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1317 : zipCycle p1317 1 23 true (1) = true := by decide +kernel
theorem never1317 (m : Machine) (hm : compatible p1317 m) : NeverHalts m :=
  zipCycle_sound p1317 1 23 true (1) (by decide) cert1317 m hm
#print axioms never1317


/-- Third-level first-hole refinement 1318, 1RB---_1RC0RE_0RD1LD_1LD1RB_---0RC_------; entry 11, period 6. -/
def p1318 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1318 : zipCycle p1318 11 6 true (1) = true := by decide +kernel
theorem never1318 (m : Machine) (hm : compatible p1318 m) : NeverHalts m :=
  zipCycle_sound p1318 11 6 true (1) (by decide) cert1318 m hm
#print axioms never1318


/-- Third-level first-hole refinement 1319, 1RB---_1RC0RE_0RD0RD_1LD1RB_---0RC_------; entry 1, period 17. -/
def p1319 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1319 : zipCycle p1319 1 17 true (1) = true := by decide +kernel
theorem never1319 (m : Machine) (hm : compatible p1319 m) : NeverHalts m :=
  zipCycle_sound p1319 1 17 true (1) (by decide) cert1319 m hm
#print axioms never1319


/-- Third-level first-hole refinement 1320, 1RB---_1RC0RE_0RD1RD_1LD1RB_---0RC_------; entry 1, period 17. -/
def p1320 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,2⟩)
  | _,_ => none
theorem cert1320 : zipCycle p1320 1 17 true (1) = true := by decide +kernel
theorem never1320 (m : Machine) (hm : compatible p1320 m) : NeverHalts m :=
  zipCycle_sound p1320 1 17 true (1) (by decide) cert1320 m hm
#print axioms never1320


/-- Third-level first-hole refinement 1321, 1RB---_1RC0RE_0RD---_1LD1RB_0LA0LD_------; entry 0, period 12. -/
def p1321 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1321 : zipCycle p1321 0 12 true (0) = true := by decide +kernel
theorem never1321 (m : Machine) (hm : compatible p1321 m) : NeverHalts m :=
  zipCycle_sound p1321 0 12 true (0) (by decide) cert1321 m hm
#print axioms never1321


/-- Third-level first-hole refinement 1322, 1RB---_1RC0RE_0RD---_1LD1RB_1LA0LD_------; entry 10, period 3. -/
def p1322 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1322 : zipCycle p1322 10 3 true (2) = true := by decide +kernel
theorem never1322 (m : Machine) (hm : compatible p1322 m) : NeverHalts m :=
  zipCycle_sound p1322 10 3 true (2) (by decide) cert1322 m hm
#print axioms never1322


/-- Third-level first-hole refinement 1323, 1RB---_1RC0RE_0RD---_1LD1RB_0RA0LD_------; entry 0, period 12. -/
def p1323 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1323 : zipCycle p1323 0 12 true (0) = true := by decide +kernel
theorem never1323 (m : Machine) (hm : compatible p1323 m) : NeverHalts m :=
  zipCycle_sound p1323 0 12 true (0) (by decide) cert1323 m hm
#print axioms never1323


/-- Third-level first-hole refinement 1324, 1RB---_1RC0RE_0RD---_1LD1RB_1RA0LD_------; entry 0, period 12. -/
def p1324 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1324 : zipCycle p1324 0 12 true (0) = true := by decide +kernel
theorem never1324 (m : Machine) (hm : compatible p1324 m) : NeverHalts m :=
  zipCycle_sound p1324 0 12 true (0) (by decide) cert1324 m hm
#print axioms never1324


/-- Third-level first-hole refinement 1325, 1RB---_1RC0RE_0RD---_1LD1RB_0LB0LD_------; entry 1, period 11. -/
def p1325 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1325 : zipCycle p1325 1 11 true (1) = true := by decide +kernel
theorem never1325 (m : Machine) (hm : compatible p1325 m) : NeverHalts m :=
  zipCycle_sound p1325 1 11 true (1) (by decide) cert1325 m hm
#print axioms never1325


/-- Third-level first-hole refinement 1326, 1RB---_1RC0RE_0RD---_1LD1RB_0RB0LD_------; entry 1, period 11. -/
def p1326 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1326 : zipCycle p1326 1 11 true (1) = true := by decide +kernel
theorem never1326 (m : Machine) (hm : compatible p1326 m) : NeverHalts m :=
  zipCycle_sound p1326 1 11 true (1) (by decide) cert1326 m hm
#print axioms never1326


/-- Third-level first-hole refinement 1327, 1RB---_1RC0RE_0RD---_1LD1RB_1RB0LD_------; entry 1, period 11. -/
def p1327 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1327 : zipCycle p1327 1 11 true (1) = true := by decide +kernel
theorem never1327 (m : Machine) (hm : compatible p1327 m) : NeverHalts m :=
  zipCycle_sound p1327 1 11 true (1) (by decide) cert1327 m hm
#print axioms never1327


/-- Third-level first-hole refinement 1328, 1RB---_1RC0RE_0RD---_1LD1RB_0LC0LD_------; entry 2, period 10. -/
def p1328 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1328 : zipCycle p1328 2 10 true (1) = true := by decide +kernel
theorem never1328 (m : Machine) (hm : compatible p1328 m) : NeverHalts m :=
  zipCycle_sound p1328 2 10 true (1) (by decide) cert1328 m hm
#print axioms never1328


/-- Third-level first-hole refinement 1329, 1RB---_1RC0RE_0RD---_1LD1RB_1LC0LD_------; entry 1, period 13. -/
def p1329 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1329 : zipCycle p1329 1 13 true (1) = true := by decide +kernel
theorem never1329 (m : Machine) (hm : compatible p1329 m) : NeverHalts m :=
  zipCycle_sound p1329 1 13 true (1) (by decide) cert1329 m hm
#print axioms never1329


/-- Third-level first-hole refinement 1330, 1RB---_1RC0RE_0RD---_1LD1RB_1RC0LD_------; entry 2, period 10. -/
def p1330 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1330 : zipCycle p1330 2 10 true (1) = true := by decide +kernel
theorem never1330 (m : Machine) (hm : compatible p1330 m) : NeverHalts m :=
  zipCycle_sound p1330 2 10 true (1) (by decide) cert1330 m hm
#print axioms never1330


/-- Third-level first-hole refinement 1331, 1RB---_1RC0RE_0RD---_1LD1RB_0LD0LD_------; entry 8, period 4. -/
def p1331 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1331 : zipCycle p1331 8 4 true (1) = true := by decide +kernel
theorem never1331 (m : Machine) (hm : compatible p1331 m) : NeverHalts m :=
  zipCycle_sound p1331 8 4 true (1) (by decide) cert1331 m hm
#print axioms never1331


/-- Third-level first-hole refinement 1332, 1RB---_1RC0RE_0RD---_1LD1RB_1LD0LD_------; entry 4, period 8. -/
def p1332 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1332 : zipCycle p1332 4 8 true (1) = true := by decide +kernel
theorem never1332 (m : Machine) (hm : compatible p1332 m) : NeverHalts m :=
  zipCycle_sound p1332 4 8 true (1) (by decide) cert1332 m hm
#print axioms never1332


/-- Third-level first-hole refinement 1333, 1RB---_1RC0RE_0RD---_1LD1RB_0RD0LD_------; entry 1, period 22. -/
def p1333 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1333 : zipCycle p1333 1 22 true (1) = true := by decide +kernel
theorem never1333 (m : Machine) (hm : compatible p1333 m) : NeverHalts m :=
  zipCycle_sound p1333 1 22 true (1) (by decide) cert1333 m hm
#print axioms never1333


/-- Third-level first-hole refinement 1334, 1RB---_1RC0RE_0RD---_1LD1RB_1RD0LD_------; entry 8, period 4. -/
def p1334 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1334 : zipCycle p1334 8 4 true (1) = true := by decide +kernel
theorem never1334 (m : Machine) (hm : compatible p1334 m) : NeverHalts m :=
  zipCycle_sound p1334 8 4 true (1) (by decide) cert1334 m hm
#print axioms never1334


/-- Third-level first-hole refinement 1335, 1RB---_1RC0RE_0RD---_1LD1RB_0LE0LD_------; entry 1, period 14. -/
def p1335 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1335 : zipCycle p1335 1 14 true (0) = true := by decide +kernel
theorem never1335 (m : Machine) (hm : compatible p1335 m) : NeverHalts m :=
  zipCycle_sound p1335 1 14 true (0) (by decide) cert1335 m hm
#print axioms never1335


/-- Third-level first-hole refinement 1336, 1RB---_1RC0RE_0RD---_1LD1RB_0RE0LD_------; entry 11, period 1. -/
def p1336 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1336 : zipCycle p1336 11 1 true (3) = true := by decide +kernel
theorem never1336 (m : Machine) (hm : compatible p1336 m) : NeverHalts m :=
  zipCycle_sound p1336 11 1 true (3) (by decide) cert1336 m hm
#print axioms never1336


/-- Third-level first-hole refinement 1337, 1RB---_1RC0RE_0RD---_1LD1RB_1RE0LD_------; entry 11, period 1. -/
def p1337 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem cert1337 : zipCycle p1337 11 1 true (3) = true := by decide +kernel
theorem never1337 (m : Machine) (hm : compatible p1337 m) : NeverHalts m :=
  zipCycle_sound p1337 11 1 true (3) (by decide) cert1337 m hm
#print axioms never1337


/-- Third-level first-hole refinement 1338, 1RB---_1RC0RE_0RD---_1LD1RB_0LA1RD_------; entry 0, period 12. -/
def p1338 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1338 : zipCycle p1338 0 12 true (0) = true := by decide +kernel
theorem never1338 (m : Machine) (hm : compatible p1338 m) : NeverHalts m :=
  zipCycle_sound p1338 0 12 true (0) (by decide) cert1338 m hm
#print axioms never1338


/-- Third-level first-hole refinement 1339, 1RB---_1RC0RE_0RD---_1LD1RB_1LA1RD_------; entry 10, period 3. -/
def p1339 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1339 : zipCycle p1339 10 3 true (4) = true := by decide +kernel
theorem never1339 (m : Machine) (hm : compatible p1339 m) : NeverHalts m :=
  zipCycle_sound p1339 10 3 true (4) (by decide) cert1339 m hm
#print axioms never1339


/-- Third-level first-hole refinement 1340, 1RB---_1RC0RE_0RD---_1LD1RB_0RA1RD_------; entry 0, period 12. -/
def p1340 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1340 : zipCycle p1340 0 12 true (0) = true := by decide +kernel
theorem never1340 (m : Machine) (hm : compatible p1340 m) : NeverHalts m :=
  zipCycle_sound p1340 0 12 true (0) (by decide) cert1340 m hm
#print axioms never1340


/-- Third-level first-hole refinement 1341, 1RB---_1RC0RE_0RD---_1LD1RB_1RA1RD_------; entry 0, period 12. -/
def p1341 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1341 : zipCycle p1341 0 12 true (0) = true := by decide +kernel
theorem never1341 (m : Machine) (hm : compatible p1341 m) : NeverHalts m :=
  zipCycle_sound p1341 0 12 true (0) (by decide) cert1341 m hm
#print axioms never1341


/-- Third-level first-hole refinement 1342, 1RB---_1RC0RE_0RD---_1LD1RB_0LB1RD_------; entry 1, period 11. -/
def p1342 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1342 : zipCycle p1342 1 11 true (1) = true := by decide +kernel
theorem never1342 (m : Machine) (hm : compatible p1342 m) : NeverHalts m :=
  zipCycle_sound p1342 1 11 true (1) (by decide) cert1342 m hm
#print axioms never1342


/-- Third-level first-hole refinement 1343, 1RB---_1RC0RE_0RD---_1LD1RB_0RB1RD_------; entry 1, period 11. -/
def p1343 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1343 : zipCycle p1343 1 11 true (1) = true := by decide +kernel
theorem never1343 (m : Machine) (hm : compatible p1343 m) : NeverHalts m :=
  zipCycle_sound p1343 1 11 true (1) (by decide) cert1343 m hm
#print axioms never1343


/-- Third-level first-hole refinement 1344, 1RB---_1RC0RE_0RD---_1LD1RB_1RB1RD_------; entry 1, period 11. -/
def p1344 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1344 : zipCycle p1344 1 11 true (1) = true := by decide +kernel
theorem never1344 (m : Machine) (hm : compatible p1344 m) : NeverHalts m :=
  zipCycle_sound p1344 1 11 true (1) (by decide) cert1344 m hm
#print axioms never1344


/-- Third-level first-hole refinement 1345, 1RB---_1RC0RE_0RD---_1LD1RB_0LC1RD_------; entry 2, period 10. -/
def p1345 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,2⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1345 : zipCycle p1345 2 10 true (1) = true := by decide +kernel
theorem never1345 (m : Machine) (hm : compatible p1345 m) : NeverHalts m :=
  zipCycle_sound p1345 2 10 true (1) (by decide) cert1345 m hm
#print axioms never1345


/-- Third-level first-hole refinement 1346, 1RB---_1RC0RE_0RD---_1LD1RB_1LC1RD_------; entry 1, period 13. -/
def p1346 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1346 : zipCycle p1346 1 13 true (1) = true := by decide +kernel
theorem never1346 (m : Machine) (hm : compatible p1346 m) : NeverHalts m :=
  zipCycle_sound p1346 1 13 true (1) (by decide) cert1346 m hm
#print axioms never1346


/-- Third-level first-hole refinement 1347, 1RB---_1RC0RE_0RD---_1LD1RB_0RC1RD_------; entry 9, period 11. -/
def p1347 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1347 : zipCycle p1347 9 11 true (3) = true := by decide +kernel
theorem never1347 (m : Machine) (hm : compatible p1347 m) : NeverHalts m :=
  zipCycle_sound p1347 9 11 true (3) (by decide) cert1347 m hm
#print axioms never1347


/-- Third-level first-hole refinement 1348, 1RB---_1RC0RE_0RD---_1LD1RB_1RC1RD_------; entry 2, period 10. -/
def p1348 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1348 : zipCycle p1348 2 10 true (1) = true := by decide +kernel
theorem never1348 (m : Machine) (hm : compatible p1348 m) : NeverHalts m :=
  zipCycle_sound p1348 2 10 true (1) (by decide) cert1348 m hm
#print axioms never1348


/-- Third-level first-hole refinement 1349, 1RB---_1RC0RE_0RD---_1LD1RB_0LD1RD_------; entry 8, period 4. -/
def p1349 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1349 : zipCycle p1349 8 4 true (3) = true := by decide +kernel
theorem never1349 (m : Machine) (hm : compatible p1349 m) : NeverHalts m :=
  zipCycle_sound p1349 8 4 true (3) (by decide) cert1349 m hm
#print axioms never1349


/-- Third-level first-hole refinement 1350, 1RB---_1RC0RE_0RD---_1LD1RB_1LD1RD_------; entry 4, period 8. -/
def p1350 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1350 : zipCycle p1350 4 8 true (1) = true := by decide +kernel
theorem never1350 (m : Machine) (hm : compatible p1350 m) : NeverHalts m :=
  zipCycle_sound p1350 4 8 true (1) (by decide) cert1350 m hm
#print axioms never1350


/-- Third-level first-hole refinement 1351, 1RB---_1RC0RE_0RD---_1LD1RB_0RD1RD_------; entry 1, period 18. -/
def p1351 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1351 : zipCycle p1351 1 18 true (1) = true := by decide +kernel
theorem never1351 (m : Machine) (hm : compatible p1351 m) : NeverHalts m :=
  zipCycle_sound p1351 1 18 true (1) (by decide) cert1351 m hm
#print axioms never1351


/-- Third-level first-hole refinement 1352, 1RB---_1RC0RE_0RD---_1LD1RB_1RD1RD_------; entry 8, period 4. -/
def p1352 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1352 : zipCycle p1352 8 4 true (3) = true := by decide +kernel
theorem never1352 (m : Machine) (hm : compatible p1352 m) : NeverHalts m :=
  zipCycle_sound p1352 8 4 true (3) (by decide) cert1352 m hm
#print axioms never1352


/-- Third-level first-hole refinement 1353, 1RB---_1RC0RE_0RD---_1LD1RB_0LE1RD_------; entry 7, period 6. -/
def p1353 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1353 : zipCycle p1353 7 6 true (3) = true := by decide +kernel
theorem never1353 (m : Machine) (hm : compatible p1353 m) : NeverHalts m :=
  zipCycle_sound p1353 7 6 true (3) (by decide) cert1353 m hm
#print axioms never1353


/-- Third-level first-hole refinement 1354, 1RB---_1RC0RE_0RD---_1LD1RB_1LE1RD_------; entry 9, period 5. -/
def p1354 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1354 : zipCycle p1354 9 5 true (3) = true := by decide +kernel
theorem never1354 (m : Machine) (hm : compatible p1354 m) : NeverHalts m :=
  zipCycle_sound p1354 9 5 true (3) (by decide) cert1354 m hm
#print axioms never1354


/-- Third-level first-hole refinement 1355, 1RB---_1RC0RE_0RD---_1LD1RB_0RE1RD_------; entry 11, period 1. -/
def p1355 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1355 : zipCycle p1355 11 1 true (5) = true := by decide +kernel
theorem never1355 (m : Machine) (hm : compatible p1355 m) : NeverHalts m :=
  zipCycle_sound p1355 11 1 true (5) (by decide) cert1355 m hm
#print axioms never1355


/-- Third-level first-hole refinement 1356, 1RB---_1RC0RE_0RD---_1LD1RB_1RE1RD_------; entry 11, period 1. -/
def p1356 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem cert1356 : zipCycle p1356 11 1 true (5) = true := by decide +kernel
theorem never1356 (m : Machine) (hm : compatible p1356 m) : NeverHalts m :=
  zipCycle_sound p1356 11 1 true (5) (by decide) cert1356 m hm
#print axioms never1356


/-- Third-level first-hole refinement 1357, 1RB---_1RC0RE_0RD---_1LD1RB_0RA0LE_------; entry 0, period 9. -/
def p1357 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1357 : zipCycle p1357 0 9 true (0) = true := by decide +kernel
theorem never1357 (m : Machine) (hm : compatible p1357 m) : NeverHalts m :=
  zipCycle_sound p1357 0 9 true (0) (by decide) cert1357 m hm
#print axioms never1357


/-- Third-level first-hole refinement 1358, 1RB---_1RC0RE_0RD---_1LD1RB_1RA0LE_------; entry 0, period 9. -/
def p1358 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1358 : zipCycle p1358 0 9 true (0) = true := by decide +kernel
theorem never1358 (m : Machine) (hm : compatible p1358 m) : NeverHalts m :=
  zipCycle_sound p1358 0 9 true (0) (by decide) cert1358 m hm
#print axioms never1358


/-- Third-level first-hole refinement 1359, 1RB---_1RC0RE_0RD---_1LD1RB_0LB0LE_------; entry 1, period 10. -/
def p1359 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1359 : zipCycle p1359 1 10 true (1) = true := by decide +kernel
theorem never1359 (m : Machine) (hm : compatible p1359 m) : NeverHalts m :=
  zipCycle_sound p1359 1 10 true (1) (by decide) cert1359 m hm
#print axioms never1359


/-- Third-level first-hole refinement 1360, 1RB---_1RC0RE_0RD---_1LD1RB_0RB0LE_------; entry 1, period 8. -/
def p1360 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1360 : zipCycle p1360 1 8 true (1) = true := by decide +kernel
theorem never1360 (m : Machine) (hm : compatible p1360 m) : NeverHalts m :=
  zipCycle_sound p1360 1 8 true (1) (by decide) cert1360 m hm
#print axioms never1360


/-- Third-level first-hole refinement 1361, 1RB---_1RC0RE_0RD---_1LD1RB_1RB0LE_------; entry 1, period 8. -/
def p1361 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1361 : zipCycle p1361 1 8 true (1) = true := by decide +kernel
theorem never1361 (m : Machine) (hm : compatible p1361 m) : NeverHalts m :=
  zipCycle_sound p1361 1 8 true (1) (by decide) cert1361 m hm
#print axioms never1361


/-- Third-level first-hole refinement 1362, 1RB---_1RC0RE_0RD---_1LD1RB_0RC0LE_------; entry 1, period 18. -/
def p1362 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1362 : zipCycle p1362 1 18 true (1) = true := by decide +kernel
theorem never1362 (m : Machine) (hm : compatible p1362 m) : NeverHalts m :=
  zipCycle_sound p1362 1 18 true (1) (by decide) cert1362 m hm
#print axioms never1362


/-- Third-level first-hole refinement 1363, 1RB---_1RC0RE_0RD---_1LD1RB_1RC0LE_------; entry 2, period 7. -/
def p1363 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1363 : zipCycle p1363 2 7 true (1) = true := by decide +kernel
theorem never1363 (m : Machine) (hm : compatible p1363 m) : NeverHalts m :=
  zipCycle_sound p1363 2 7 true (1) (by decide) cert1363 m hm
#print axioms never1363


/-- Third-level first-hole refinement 1364, 1RB---_1RC0RE_0RD---_1LD1RB_0LD0LE_------; entry 1, period 9. -/
def p1364 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1364 : zipCycle p1364 1 9 true (1) = true := by decide +kernel
theorem never1364 (m : Machine) (hm : compatible p1364 m) : NeverHalts m :=
  zipCycle_sound p1364 1 9 true (1) (by decide) cert1364 m hm
#print axioms never1364


/-- Third-level first-hole refinement 1365, 1RB---_1RC0RE_0RD---_1LD1RB_1LD0LE_------; entry 4, period 8. -/
def p1365 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1365 : zipCycle p1365 4 8 true (1) = true := by decide +kernel
theorem never1365 (m : Machine) (hm : compatible p1365 m) : NeverHalts m :=
  zipCycle_sound p1365 4 8 true (1) (by decide) cert1365 m hm
#print axioms never1365


/-- Third-level first-hole refinement 1366, 1RB---_1RC0RE_0RD---_1LD1RB_0RD0LE_------; entry 3, period 6. -/
def p1366 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1366 : zipCycle p1366 3 6 true (1) = true := by decide +kernel
theorem never1366 (m : Machine) (hm : compatible p1366 m) : NeverHalts m :=
  zipCycle_sound p1366 3 6 true (1) (by decide) cert1366 m hm
#print axioms never1366


/-- Third-level first-hole refinement 1367, 1RB---_1RC0RE_0RD---_1LD1RB_1RD0LE_------; entry 8, period 4. -/
def p1367 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1367 : zipCycle p1367 8 4 true (2) = true := by decide +kernel
theorem never1367 (m : Machine) (hm : compatible p1367 m) : NeverHalts m :=
  zipCycle_sound p1367 8 4 true (2) (by decide) cert1367 m hm
#print axioms never1367


/-- Third-level first-hole refinement 1368, 1RB---_1RC0RE_0RD---_1LD1RB_0LE0LE_------; entry 11, period 1. -/
def p1368 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1368 : zipCycle p1368 11 1 false (-1) = true := by decide +kernel
theorem never1368 (m : Machine) (hm : compatible p1368 m) : NeverHalts m :=
  zipCycle_sound p1368 11 1 false (-1) (by decide) cert1368 m hm
#print axioms never1368


/-- Third-level first-hole refinement 1369, 1RB---_1RC0RE_0RD---_1LD1RB_1LE0LE_------; entry 11, period 1. -/
def p1369 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1369 : zipCycle p1369 11 1 false (-1) = true := by decide +kernel
theorem never1369 (m : Machine) (hm : compatible p1369 m) : NeverHalts m :=
  zipCycle_sound p1369 11 1 false (-1) (by decide) cert1369 m hm
#print axioms never1369


/-- Third-level first-hole refinement 1370, 1RB---_1RC0RE_0RD---_1LD1RB_0RE0LE_------; entry 8, period 1. -/
def p1370 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1370 : zipCycle p1370 8 1 true (2) = true := by decide +kernel
theorem never1370 (m : Machine) (hm : compatible p1370 m) : NeverHalts m :=
  zipCycle_sound p1370 8 1 true (2) (by decide) cert1370 m hm
#print axioms never1370


/-- Third-level first-hole refinement 1371, 1RB---_1RC0RE_0RD---_1LD1RB_1RE0LE_------; entry 8, period 1. -/
def p1371 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,false,4⟩)
  | _,_ => none
theorem cert1371 : zipCycle p1371 8 1 true (2) = true := by decide +kernel
theorem never1371 (m : Machine) (hm : compatible p1371 m) : NeverHalts m :=
  zipCycle_sound p1371 8 1 true (2) (by decide) cert1371 m hm
#print axioms never1371


/-- Third-level first-hole refinement 1372, 1RB---_1RC0RE_0RD---_1LD1RB_0LB1LE_------; entry 1, period 13. -/
def p1372 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1372 : zipCycle p1372 1 13 true (1) = true := by decide +kernel
theorem never1372 (m : Machine) (hm : compatible p1372 m) : NeverHalts m :=
  zipCycle_sound p1372 1 13 true (1) (by decide) cert1372 m hm
#print axioms never1372


/-- Third-level first-hole refinement 1373, 1RB---_1RC0RE_0RD---_1LD1RB_0RB1LE_------; entry 1, period 10. -/
def p1373 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1373 : zipCycle p1373 1 10 true (1) = true := by decide +kernel
theorem never1373 (m : Machine) (hm : compatible p1373 m) : NeverHalts m :=
  zipCycle_sound p1373 1 10 true (1) (by decide) cert1373 m hm
#print axioms never1373


/-- Third-level first-hole refinement 1374, 1RB---_1RC0RE_0RD---_1LD1RB_1RB1LE_------; entry 1, period 10. -/
def p1374 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1374 : zipCycle p1374 1 10 true (1) = true := by decide +kernel
theorem never1374 (m : Machine) (hm : compatible p1374 m) : NeverHalts m :=
  zipCycle_sound p1374 1 10 true (1) (by decide) cert1374 m hm
#print axioms never1374


/-- Third-level first-hole refinement 1375, 1RB---_1RC0RE_0RD---_1LD1RB_1LD1LE_------; entry 5, period 4. -/
def p1375 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1375 : zipCycle p1375 5 4 true (1) = true := by decide +kernel
theorem never1375 (m : Machine) (hm : compatible p1375 m) : NeverHalts m :=
  zipCycle_sound p1375 5 4 true (1) (by decide) cert1375 m hm
#print axioms never1375


/-- Third-level first-hole refinement 1376, 1RB---_1RC0RE_0RD---_1LD1RB_0RD1LE_------; entry 1, period 9. -/
def p1376 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1376 : zipCycle p1376 1 9 true (1) = true := by decide +kernel
theorem never1376 (m : Machine) (hm : compatible p1376 m) : NeverHalts m :=
  zipCycle_sound p1376 1 9 true (1) (by decide) cert1376 m hm
#print axioms never1376


/-- Third-level first-hole refinement 1377, 1RB---_1RC0RE_0RD---_1LD1RB_1RD1LE_------; entry 1, period 9. -/
def p1377 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1377 : zipCycle p1377 1 9 true (1) = true := by decide +kernel
theorem never1377 (m : Machine) (hm : compatible p1377 m) : NeverHalts m :=
  zipCycle_sound p1377 1 9 true (1) (by decide) cert1377 m hm
#print axioms never1377


/-- Third-level first-hole refinement 1378, 1RB---_1RC0RE_0RD---_1LD1RB_0LE1LE_------; entry 11, period 1. -/
def p1378 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1378 : zipCycle p1378 11 1 false (-1) = true := by decide +kernel
theorem never1378 (m : Machine) (hm : compatible p1378 m) : NeverHalts m :=
  zipCycle_sound p1378 11 1 false (-1) (by decide) cert1378 m hm
#print axioms never1378


/-- Third-level first-hole refinement 1379, 1RB---_1RC0RE_0RD---_1LD1RB_1LE1LE_------; entry 11, period 1. -/
def p1379 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1379 : zipCycle p1379 11 1 false (-1) = true := by decide +kernel
theorem never1379 (m : Machine) (hm : compatible p1379 m) : NeverHalts m :=
  zipCycle_sound p1379 11 1 false (-1) (by decide) cert1379 m hm
#print axioms never1379


/-- Third-level first-hole refinement 1380, 1RB---_1RC0RE_0RD---_1LD1RB_0RE1LE_------; entry 7, period 2. -/
def p1380 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1380 : zipCycle p1380 7 2 true (2) = true := by decide +kernel
theorem never1380 (m : Machine) (hm : compatible p1380 m) : NeverHalts m :=
  zipCycle_sound p1380 7 2 true (2) (by decide) cert1380 m hm
#print axioms never1380


/-- Third-level first-hole refinement 1381, 1RB---_1RC0RE_0RD---_1LD1RB_1RE1LE_------; entry 11, period 3. -/
def p1381 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨true,false,4⟩)
  | _,_ => none
theorem cert1381 : zipCycle p1381 11 3 false (1) = true := by decide +kernel
theorem never1381 (m : Machine) (hm : compatible p1381 m) : NeverHalts m :=
  zipCycle_sound p1381 11 3 false (1) (by decide) cert1381 m hm
#print axioms never1381


/-- Third-level first-hole refinement 1382, 1RB---_1RC0RE_0RD---_1LD1RB_0LA0RE_------; entry 0, period 9. -/
def p1382 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1382 : zipCycle p1382 0 9 true (0) = true := by decide +kernel
theorem never1382 (m : Machine) (hm : compatible p1382 m) : NeverHalts m :=
  zipCycle_sound p1382 0 9 true (0) (by decide) cert1382 m hm
#print axioms never1382


/-- Third-level first-hole refinement 1383, 1RB---_1RC0RE_0RD---_1LD1RB_1LA0RE_------; entry 8, period 3. -/
def p1383 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1383 : zipCycle p1383 8 3 true (3) = true := by decide +kernel
theorem never1383 (m : Machine) (hm : compatible p1383 m) : NeverHalts m :=
  zipCycle_sound p1383 8 3 true (3) (by decide) cert1383 m hm
#print axioms never1383


/-- Third-level first-hole refinement 1384, 1RB---_1RC0RE_0RD---_1LD1RB_0RA0RE_------; entry 0, period 9. -/
def p1384 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1384 : zipCycle p1384 0 9 true (0) = true := by decide +kernel
theorem never1384 (m : Machine) (hm : compatible p1384 m) : NeverHalts m :=
  zipCycle_sound p1384 0 9 true (0) (by decide) cert1384 m hm
#print axioms never1384


/-- Third-level first-hole refinement 1385, 1RB---_1RC0RE_0RD---_1LD1RB_1RA0RE_------; entry 0, period 9. -/
def p1385 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1385 : zipCycle p1385 0 9 true (0) = true := by decide +kernel
theorem never1385 (m : Machine) (hm : compatible p1385 m) : NeverHalts m :=
  zipCycle_sound p1385 0 9 true (0) (by decide) cert1385 m hm
#print axioms never1385


/-- Third-level first-hole refinement 1386, 1RB---_1RC0RE_0RD---_1LD1RB_0LB0RE_------; entry 1, period 8. -/
def p1386 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1386 : zipCycle p1386 1 8 true (1) = true := by decide +kernel
theorem never1386 (m : Machine) (hm : compatible p1386 m) : NeverHalts m :=
  zipCycle_sound p1386 1 8 true (1) (by decide) cert1386 m hm
#print axioms never1386


/-- Third-level first-hole refinement 1387, 1RB---_1RC0RE_0RD---_1LD1RB_0RB0RE_------; entry 1, period 8. -/
def p1387 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1387 : zipCycle p1387 1 8 true (1) = true := by decide +kernel
theorem never1387 (m : Machine) (hm : compatible p1387 m) : NeverHalts m :=
  zipCycle_sound p1387 1 8 true (1) (by decide) cert1387 m hm
#print axioms never1387


/-- Third-level first-hole refinement 1388, 1RB---_1RC0RE_0RD---_1LD1RB_1RB0RE_------; entry 1, period 8. -/
def p1388 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,1⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1388 : zipCycle p1388 1 8 true (1) = true := by decide +kernel
theorem never1388 (m : Machine) (hm : compatible p1388 m) : NeverHalts m :=
  zipCycle_sound p1388 1 8 true (1) (by decide) cert1388 m hm
#print axioms never1388


/-- Third-level first-hole refinement 1389, 1RB---_1RC0RE_0RD---_1LD1RB_1LC0RE_------; entry 1, period 10. -/
def p1389 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1389 : zipCycle p1389 1 10 true (1) = true := by decide +kernel
theorem never1389 (m : Machine) (hm : compatible p1389 m) : NeverHalts m :=
  zipCycle_sound p1389 1 10 true (1) (by decide) cert1389 m hm
#print axioms never1389


/-- Third-level first-hole refinement 1390, 1RB---_1RC0RE_0RD---_1LD1RB_1RC0RE_------; entry 2, period 7. -/
def p1390 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,2⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1390 : zipCycle p1390 2 7 true (1) = true := by decide +kernel
theorem never1390 (m : Machine) (hm : compatible p1390 m) : NeverHalts m :=
  zipCycle_sound p1390 2 7 true (1) (by decide) cert1390 m hm
#print axioms never1390


/-- Third-level first-hole refinement 1391, 1RB---_1RC0RE_0RD---_1LD1RB_0LD0RE_------; entry 3, period 6. -/
def p1391 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1391 : zipCycle p1391 3 6 true (1) = true := by decide +kernel
theorem never1391 (m : Machine) (hm : compatible p1391 m) : NeverHalts m :=
  zipCycle_sound p1391 3 6 true (1) (by decide) cert1391 m hm
#print axioms never1391


/-- Third-level first-hole refinement 1392, 1RB---_1RC0RE_0RD---_1LD1RB_1RD0RE_------; entry 8, period 4. -/
def p1392 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,3⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1392 : zipCycle p1392 8 4 true (4) = true := by decide +kernel
theorem never1392 (m : Machine) (hm : compatible p1392 m) : NeverHalts m :=
  zipCycle_sound p1392 8 4 true (4) (by decide) cert1392 m hm
#print axioms never1392


/-- Third-level first-hole refinement 1393, 1RB---_1RC0RE_0RD---_1LD1RB_0LE0RE_------; entry 15, period 1. -/
def p1393 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1393 : zipCycle p1393 15 1 false (1) = true := by decide +kernel
theorem never1393 (m : Machine) (hm : compatible p1393 m) : NeverHalts m :=
  zipCycle_sound p1393 15 1 false (1) (by decide) cert1393 m hm
#print axioms never1393


/-- Third-level first-hole refinement 1394, 1RB---_1RC0RE_0RD---_1LD1RB_1LE0RE_------; entry 26, period 1. -/
def p1394 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,false,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1394 : zipCycle p1394 26 1 false (6) = true := by decide +kernel
theorem never1394 (m : Machine) (hm : compatible p1394 m) : NeverHalts m :=
  zipCycle_sound p1394 26 1 false (6) (by decide) cert1394 m hm
#print axioms never1394


/-- Third-level first-hole refinement 1395, 1RB---_1RC0RE_0RD---_1LD1RB_0RE0RE_------; entry 8, period 1. -/
def p1395 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1395 : zipCycle p1395 8 1 true (4) = true := by decide +kernel
theorem never1395 (m : Machine) (hm : compatible p1395 m) : NeverHalts m :=
  zipCycle_sound p1395 8 1 true (4) (by decide) cert1395 m hm
#print axioms never1395


/-- Third-level first-hole refinement 1396, 1RB---_1RC0RE_0RD---_1LD1RB_1RE0RE_------; entry 8, period 1. -/
def p1396 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,4⟩)
  | 4, true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem cert1396 : zipCycle p1396 8 1 true (4) = true := by decide +kernel
theorem never1396 (m : Machine) (hm : compatible p1396 m) : NeverHalts m :=
  zipCycle_sound p1396 8 1 true (4) (by decide) cert1396 m hm
#print axioms never1396


/-- Third-level first-hole refinement 1397, 1RB---_1RC0RE_0RD---_1LD1RB_0RA1RE_------; entry 0, period 9. -/
def p1397 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,true,0⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1397 : zipCycle p1397 0 9 true (0) = true := by decide +kernel
theorem never1397 (m : Machine) (hm : compatible p1397 m) : NeverHalts m :=
  zipCycle_sound p1397 0 9 true (0) (by decide) cert1397 m hm
#print axioms never1397


/-- Third-level first-hole refinement 1398, 1RB---_1RC0RE_0RD---_1LD1RB_1RA1RE_------; entry 0, period 9. -/
def p1398 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨true,true,0⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1398 : zipCycle p1398 0 9 true (0) = true := by decide +kernel
theorem never1398 (m : Machine) (hm : compatible p1398 m) : NeverHalts m :=
  zipCycle_sound p1398 0 9 true (0) (by decide) cert1398 m hm
#print axioms never1398


/-- Third-level first-hole refinement 1399, 1RB---_1RC0RE_0RD---_1LD1RB_0LB1RE_------; entry 1, period 10. -/
def p1399 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,4⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,true,1⟩)
  | 4, false => some (some ⟨false,false,1⟩)
  | 4, true => some (some ⟨true,true,4⟩)
  | _,_ => none
theorem cert1399 : zipCycle p1399 1 10 true (1) = true := by decide +kernel
theorem never1399 (m : Machine) (hm : compatible p1399 m) : NeverHalts m :=
  zipCycle_sound p1399 1 10 true (1) (by decide) cert1399 m hm
#print axioms never1399

end BB6.Agent24Raw45D3_13
