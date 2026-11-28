import Raw40OrientedCrossing
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing.C1LBM143
open BB6Coverage Agent42Crossing Agent19OrientedCrossing
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 36978 60644 [(11,231)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 36978 (-240) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 36978 (-240) checkedCert m hm
#print axioms never
end BB6Coverage.Agent19Raw40LateCrossing.C1LBM143
