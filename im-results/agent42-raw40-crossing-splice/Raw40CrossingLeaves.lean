import CrossingGenerate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent42Raw40Crossing
open BB6Coverage Agent42Crossing
namespace C1RBM71
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def cert : Certificate := witness table 362 468 [(10,30)]
theorem checkedCert : checked table cert 362 (-10) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 362 (-10) checkedCert m hm
#print axioms never
end C1RBM71
namespace C1RBM74
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | _,_ => none
def cert : Certificate := witness table 362 468 [(10,30)]
theorem checkedCert : checked table cert 362 (-10) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 362 (-10) checkedCert m hm
#print axioms never
end C1RBM74
namespace C1RBM75
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none
def cert : Certificate := witness table 336 430 [(10,30)]
theorem checkedCert : checked table cert 336 (-10) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 336 (-10) checkedCert m hm
#print axioms never
end C1RBM75
namespace C1RBM153
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def cert : Certificate := witness table 320 364 [(3,15), (23,28)]
theorem checkedCert : checked table cert 320 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 320 (-14) checkedCert m hm
#print axioms never
end C1RBM153
namespace C1RBM154
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | _,_ => none
def cert : Certificate := witness table 324 368 [(3,9), (14,24)]
theorem checkedCert : checked table cert 324 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 324 (-14) checkedCert m hm
#print axioms never
end C1RBM154
namespace C1RBM155
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | _,_ => none
def cert : Certificate := witness table 1689 652 [(6,12), (60,66)]
theorem checkedCert : checked table cert 1689 (-41) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 1689 (-41) checkedCert m hm
#print axioms never
end C1RBM155
namespace C1RBM156
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none
def cert : Certificate := witness table 586 262 [(3,9), (32,38)]
theorem checkedCert : checked table cert 586 (-18) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 586 (-18) checkedCert m hm
#print axioms never
end C1RBM156
namespace C1RBM157
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | _,_ => none
def cert : Certificate := witness table 634 290 [(3,9), (24,32)]
theorem checkedCert : checked table cert 634 (-18) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 634 (-18) checkedCert m hm
#print axioms never
end C1RBM157
namespace C1RBM158
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | _,_ => none
def cert : Certificate := witness table 310 342 [(3,15), (28,31)]
theorem checkedCert : checked table cert 310 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 310 (-14) checkedCert m hm
#print axioms never
end C1RBM158
namespace C1RBM159
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | _,_ => none
def cert : Certificate := witness table 320 364 [(3,9), (14,24)]
theorem checkedCert : checked table cert 320 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 320 (-14) checkedCert m hm
#print axioms never
end C1RBM159
namespace C1RBM160
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none
def cert : Certificate := witness table 544 236 [(3,9), (27,32)]
theorem checkedCert : checked table cert 544 (-18) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 544 (-18) checkedCert m hm
#print axioms never
end C1RBM160
namespace C1RBM161
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none
def cert : Certificate := witness table 502 210 [(3,9), (32,35)]
theorem checkedCert : checked table cert 502 (-18) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 502 (-18) checkedCert m hm
#print axioms never
end C1RBM161
namespace C1RBM185
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def cert : Certificate := witness table 309 776 [(2,14), (14,30)]
theorem checkedCert : checked table cert 309 (-15) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 309 (-15) checkedCert m hm
#print axioms never
end C1RBM185
namespace C1RBM186
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨false,false,2⟩)
  | _,_ => none
def cert : Certificate := witness table 320 364 [(3,15), (23,28)]
theorem checkedCert : checked table cert 320 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 320 (-14) checkedCert m hm
#print axioms never
end C1RBM186
namespace C1RBM188
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none
def cert : Certificate := witness table 88 92 [(3,9)]
theorem checkedCert : checked table cert 88 (-6) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 88 (-6) checkedCert m hm
#print axioms never
end C1RBM188
namespace C1RBM189
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,3⟩)
  | _,_ => none
def cert : Certificate := witness table 324 368 [(3,9), (14,24)]
theorem checkedCert : checked table cert 324 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 324 (-14) checkedCert m hm
#print axioms never
end C1RBM189
namespace C1RBM190
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none
def cert : Certificate := witness table 550 238 [(3,9), (27,32)]
theorem checkedCert : checked table cert 550 (-18) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 550 (-18) checkedCert m hm
#print axioms never
end C1RBM190
namespace C1RBM191
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,1⟩)
  | _,_ => none
def cert : Certificate := witness table 308 340 [(3,15), (28,31)]
theorem checkedCert : checked table cert 308 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 308 (-14) checkedCert m hm
#print axioms never
end C1RBM191
namespace C1RBM192
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none
def cert : Certificate := witness table 318 362 [(3,15), (23,28)]
theorem checkedCert : checked table cert 318 (-14) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 318 (-14) checkedCert m hm
#print axioms never
end C1RBM192
namespace C1RBM193
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none
def cert : Certificate := witness table 3392 2516 [(5,35), (90,95)]
theorem checkedCert : checked table cert 3392 (-56) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 3392 (-56) checkedCert m hm
#print axioms never
end C1RBM193
namespace C0RDM71
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨false,false,0⟩)
  | _,_ => none
def cert : Certificate := witness table 374 486 [(10,30)]
theorem checkedCert : checked table cert 374 (-10) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 374 (-10) checkedCert m hm
#print axioms never
end C0RDM71
namespace C0RDM73
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,false => some (some ⟨true,true,2⟩)
  | _,_ => none
def cert : Certificate := witness table 348 448 [(10,30)]
theorem checkedCert : checked table cert 348 (-10) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 348 (-10) checkedCert m hm
#print axioms never
end C0RDM73
namespace C1LAM156
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨false,true,2⟩)
  | _,_ => none
def cert : Certificate := witness table 2340 2172 [(5,26), (63,84)]
theorem checkedCert : checked table cert 2340 (-42) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent42Crossing.never table cert 2340 (-42) checkedCert m hm
#print axioms never
end C1LAM156
end BB6Coverage.Agent42Raw40Crossing
