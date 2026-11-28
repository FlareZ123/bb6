import ZipAuditCore
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace BB6.Agent16Raw44Easy13
open BB6Coverage BB6Coverage.Agent10ZipAudit

/- Thirteen first-hole Raw44 C1 siblings, each 25^5 total tables,
  distinguished by exact fixed partial transition C1. -/
/-- Raw44 B1=0RC, C1=0LB; translated left side-cycle at raw 49, period 1. -/
def p0 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle0 : zipCycle p0 49 1 false (5) = true := by decide +kernel
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m :=
  zipCycle_sound p0 49 1 false (5) (by decide) cycle0 m hm
theorem cover0 (bound : Nat) : Cover (DecidedBelow bound) p0 :=
  Cover.leaf p0 (fun m hm => Or.inl (never0 m hm))
#print axioms never0
#print axioms cover0

/-- Raw44 B1=0RC, C1=0LC; translated left side-cycle at raw 9, period 1. -/
def p1 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle1 : zipCycle p1 9 1 false (1) = true := by decide +kernel
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m :=
  zipCycle_sound p1 9 1 false (1) (by decide) cycle1 m hm
theorem cover1 (bound : Nat) : Cover (DecidedBelow bound) p1 :=
  Cover.leaf p1 (fun m hm => Or.inl (never1 m hm))
#print axioms never1
#print axioms cover1

/-- Raw44 B1=0RC, C1=0LD; translated left side-cycle at raw 8, period 1. -/
def p2 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle2 : zipCycle p2 8 1 false (0) = true := by decide +kernel
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m :=
  zipCycle_sound p2 8 1 false (0) (by decide) cycle2 m hm
theorem cover2 (bound : Nat) : Cover (DecidedBelow bound) p2 :=
  Cover.leaf p2 (fun m hm => Or.inl (never2 m hm))
#print axioms never2
#print axioms cover2

/-- Raw44 B1=0RC, C1=0RB; translated right side-cycle at raw 7, period 9. -/
def p3 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle3 : zipCycle p3 7 9 true (1) = true := by decide +kernel
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m :=
  zipCycle_sound p3 7 9 true (1) (by decide) cycle3 m hm
theorem cover3 (bound : Nat) : Cover (DecidedBelow bound) p3 :=
  Cover.leaf p3 (fun m hm => Or.inl (never3 m hm))
#print axioms never3
#print axioms cover3

/-- Raw44 B1=0RC, C1=0RC; translated left side-cycle at raw 11, period 1. -/
def p4 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle4 : zipCycle p4 11 1 false (5) = true := by decide +kernel
theorem never4 (m : Machine) (hm : compatible p4 m) : NeverHalts m :=
  zipCycle_sound p4 11 1 false (5) (by decide) cycle4 m hm
theorem cover4 (bound : Nat) : Cover (DecidedBelow bound) p4 :=
  Cover.leaf p4 (fun m hm => Or.inl (never4 m hm))
#print axioms never4
#print axioms cover4

/-- Raw44 B1=0RC, C1=0RD; translated right side-cycle at raw 3, period 11. -/
def p5 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨false,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle5 : zipCycle p5 3 11 true (0) = true := by decide +kernel
theorem never5 (m : Machine) (hm : compatible p5 m) : NeverHalts m :=
  zipCycle_sound p5 3 11 true (0) (by decide) cycle5 m hm
theorem cover5 (bound : Nat) : Cover (DecidedBelow bound) p5 :=
  Cover.leaf p5 (fun m hm => Or.inl (never5 m hm))
#print axioms never5
#print axioms cover5

/-- Raw44 B1=0RC, C1=1LA; translated right side-cycle at raw 6, period 18. -/
def p6 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,0⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle6 : zipCycle p6 6 18 true (0) = true := by decide +kernel
theorem never6 (m : Machine) (hm : compatible p6 m) : NeverHalts m :=
  zipCycle_sound p6 6 18 true (0) (by decide) cycle6 m hm
theorem cover6 (bound : Nat) : Cover (DecidedBelow bound) p6 :=
  Cover.leaf p6 (fun m hm => Or.inl (never6 m hm))
#print axioms never6
#print axioms cover6

/-- Raw44 B1=0RC, C1=1LB; translated right side-cycle at raw 6, period 4. -/
def p7 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle7 : zipCycle p7 6 4 true (0) = true := by decide +kernel
theorem never7 (m : Machine) (hm : compatible p7 m) : NeverHalts m :=
  zipCycle_sound p7 6 4 true (0) (by decide) cycle7 m hm
theorem cover7 (bound : Nat) : Cover (DecidedBelow bound) p7 :=
  Cover.leaf p7 (fun m hm => Or.inl (never7 m hm))
#print axioms never7
#print axioms cover7

/-- Raw44 B1=0RC, C1=1LC; translated left side-cycle at raw 7, period 5. -/
def p8 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle8 : zipCycle p8 7 5 false (1) = true := by decide +kernel
theorem never8 (m : Machine) (hm : compatible p8 m) : NeverHalts m :=
  zipCycle_sound p8 7 5 false (1) (by decide) cycle8 m hm
theorem cover8 (bound : Nat) : Cover (DecidedBelow bound) p8 :=
  Cover.leaf p8 (fun m hm => Or.inl (never8 m hm))
#print axioms never8
#print axioms cover8

/-- Raw44 B1=0RC, C1=1LD; translated left side-cycle at raw 8, period 1. -/
def p9 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,false,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle9 : zipCycle p9 8 1 false (0) = true := by decide +kernel
theorem never9 (m : Machine) (hm : compatible p9 m) : NeverHalts m :=
  zipCycle_sound p9 8 1 false (0) (by decide) cycle9 m hm
theorem cover9 (bound : Nat) : Cover (DecidedBelow bound) p9 :=
  Cover.leaf p9 (fun m hm => Or.inl (never9 m hm))
#print axioms never9
#print axioms cover9

/-- Raw44 B1=0RC, C1=1RB; translated right side-cycle at raw 1, period 9. -/
def p10 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,1⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle10 : zipCycle p10 1 9 true (0) = true := by decide +kernel
theorem never10 (m : Machine) (hm : compatible p10 m) : NeverHalts m :=
  zipCycle_sound p10 1 9 true (0) (by decide) cycle10 m hm
theorem cover10 (bound : Nat) : Cover (DecidedBelow bound) p10 :=
  Cover.leaf p10 (fun m hm => Or.inl (never10 m hm))
#print axioms never10
#print axioms cover10

/-- Raw44 B1=0RC, C1=1RC; translated right side-cycle at raw 2, period 8. -/
def p11 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,2⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle11 : zipCycle p11 2 8 true (0) = true := by decide +kernel
theorem never11 (m : Machine) (hm : compatible p11 m) : NeverHalts m :=
  zipCycle_sound p11 2 8 true (0) (by decide) cycle11 m hm
theorem cover11 (bound : Nat) : Cover (DecidedBelow bound) p11 :=
  Cover.leaf p11 (fun m hm => Or.inl (never11 m hm))
#print axioms never11
#print axioms cover11

/-- Raw44 B1=0RC, C1=1RD; translated right side-cycle at raw 10, period 7. -/
def p12 : PartialMachine := fun t => match t.1.val,t.2 with
  | 0, false => some (some ⟨true,true,1⟩)
  | 1, false => some (some ⟨true,true,2⟩)
  | 1, true => some (some ⟨false,true,2⟩)
  | 2, false => some (some ⟨false,true,3⟩)
  | 2, true => some (some ⟨true,true,3⟩)
  | 3, false => some (some ⟨true,false,3⟩)
  | 3, true => some (some ⟨true,false,1⟩)
  | _,_ => none

theorem cycle12 : zipCycle p12 10 7 true (2) = true := by decide +kernel
theorem never12 (m : Machine) (hm : compatible p12 m) : NeverHalts m :=
  zipCycle_sound p12 10 7 true (2) (by decide) cycle12 m hm
theorem cover12 (bound : Nat) : Cover (DecidedBelow bound) p12 :=
  Cover.leaf p12 (fun m hm => Or.inl (never12 m hm))
#print axioms never12
#print axioms cover12

end BB6.Agent16Raw44Easy13
