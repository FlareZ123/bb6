import ZipAuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent42Raw40LongCycles
open BB6Coverage BB6Coverage.Agent10ZipAudit

namespace C1LCM201
-- 1RB0LA_1RC1RE_0RD1LC_1LD1LA_0RF0RC_1RD---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none
theorem checked : zipCycle table 0 868 false (15) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zipCycle_sound table 0 868 false (15) (by decide) checked m hm
#print axioms never
end C1LCM201

namespace C1RCM160
-- 1RB0LA_1RC1RE_0RD1RC_1LD1LA_0RD0RF_---0RE
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
theorem checked : zipCycle table 0 404 false (15) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zipCycle_sound table 0 404 false (15) (by decide) checked m hm
#print axioms never
end C1RCM160

namespace C1RBM54
-- 1RB0LA_1RC0RE_0RD1RB_1LD1LA_---0RF_1LB0LD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none
theorem checked : zipCycle table 381 354 false (4) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zipCycle_sound table 381 354 false (4) (by decide) checked m hm
#print axioms never
end C1RBM54

namespace C0RDM150
-- 1RB0LA_1RC1RE_0RD0RD_1LD1LA_---0RF_0LA0RA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none
theorem checked : zipCycle table 905 288 false (5) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zipCycle_sound table 905 288 false (5) (by decide) checked m hm
#print axioms never
end C0RDM150

namespace C1LAM161
-- 1RB0LA_1RC1RE_0RD1LA_1LD1LA_0RB0RF_---0RD
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
theorem checked : zipCycle table 628 356 false (5) = true := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  zipCycle_sound table 628 356 false (5) (by decide) checked m hm
#print axioms never
end C1LAM161
end BB6.Agent42Raw40LongCycles
