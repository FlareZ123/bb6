import Raw40OrientedCrossing
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing
open BB6Coverage Agent42Crossing Agent19OrientedCrossing
namespace C0LEM366
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 729 494 [(3,15)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 729 (-15) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 729 (-15) checkedCert m hm
#print axioms never
end C0LEM366

namespace C0REM759
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 1243 1466 [(3,23)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 1243 (-15) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 1243 (-15) checkedCert m hm
#print axioms never
end C0REM759

namespace C0REM792
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,2⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 1129 1312 [(3,23)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 1129 (-15) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 1129 (-15) checkedCert m hm
#print axioms never
end C0REM792

namespace C0REM790
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 2198 444 [(15,17), (30,36)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 2198 (-48) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 2198 (-48) checkedCert m hm
#print axioms never
end C0REM790

end BB6Coverage.Agent19Raw40LateCrossing
