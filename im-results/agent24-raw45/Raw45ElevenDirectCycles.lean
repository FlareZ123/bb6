import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent24Raw45DirectCycles
open BB6Coverage BB6Coverage.Agent10ZipAudit

/-- A1=0LA, B1=0LA, exact entry0, period9. -/
def p0 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert0 : zipCycle p0 0 9 false (3) = true := by decide +kernel
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m :=
  zipCycle_sound p0 0 9 false (3) (by decide) cert0 m hm
#print axioms never0

/-- A1=1LA, B1=0LA, exact entry8, period3. -/
def p1 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert1 : zipCycle p1 8 3 false (0) = true := by decide +kernel
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m :=
  zipCycle_sound p1 8 3 false (0) (by decide) cert1 m hm
#print axioms never1

/-- A1=0RA, B1=0LA, exact entry0, period11. -/
def p2 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert2 : zipCycle p2 0 11 true (0) = true := by decide +kernel
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m :=
  zipCycle_sound p2 0 11 true (0) (by decide) cert2 m hm
#print axioms never2

/-- A1=1RA, B1=0LA, exact entry0, period11. -/
def p3 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert3 : zipCycle p3 0 11 true (0) = true := by decide +kernel
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m :=
  zipCycle_sound p3 0 11 true (0) (by decide) cert3 m hm
#print axioms never3

/-- A1=0LB, B1=0LA, exact entry0, period9. -/
def p4 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert4 : zipCycle p4 0 9 false (3) = true := by decide +kernel
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m :=
  zipCycle_sound p4 0 9 false (3) (by decide) cert4 m hm
#print axioms never4

/-- A1=0RC, B1=0LA, exact entry1, period9. -/
def p5 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert5 : zipCycle p5 1 9 true (1) = true := by decide +kernel
theorem never5 (m : Machine) (hm : compatible p5 m) : NeverHalts m :=
  zipCycle_sound p5 1 9 true (1) (by decide) cert5 m hm
#print axioms never5

/-- A1=1RC, B1=0LA, exact entry1, period9. -/
def p6 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert6 : zipCycle p6 1 9 true (1) = true := by decide +kernel
theorem never6 (m : Machine) (hm : compatible p6 m) : NeverHalts m :=
  zipCycle_sound p6 1 9 true (1) (by decide) cert6 m hm
#print axioms never6

/-- A1=0LD, B1=0LA, exact entry1, period11. -/
def p7 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert7 : zipCycle p7 1 11 true (0) = true := by decide +kernel
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m :=
  zipCycle_sound p7 1 11 true (0) (by decide) cert7 m hm
#print axioms never7

/-- A1=1LD, B1=0LA, exact entry11, period1. -/
def p8 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert8 : zipCycle p8 11 1 false (-1) = true := by decide +kernel
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m :=
  zipCycle_sound p8 11 1 false (-1) (by decide) cert8 m hm
#print axioms never8

/-- A1=0RD, B1=0LA, exact entry13, period1. -/
def p9 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert9 : zipCycle p9 13 1 false (1) = true := by decide +kernel
theorem never9 (m : Machine) (hm : compatible p9 m) : NeverHalts m :=
  zipCycle_sound p9 13 1 false (1) (by decide) cert9 m hm
#print axioms never9

/-- A1=1RD, B1=0LA, exact entry4, period4. -/
def p10 : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none

theorem cert10 : zipCycle p10 4 4 true (1) = true := by decide +kernel
theorem never10 (m : Machine) (hm : compatible p10 m) : NeverHalts m :=
  zipCycle_sound p10 4 4 true (1) (by decide) cert10 m hm
#print axioms never10
end BB6.Agent24Raw45DirectCycles
