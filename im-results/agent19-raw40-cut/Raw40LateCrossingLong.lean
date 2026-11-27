import Raw40OrientedCrossing
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing
open BB6Coverage Agent42Crossing Agent19OrientedCrossing
namespace C0REM1730
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial true false table
def cert : Certificate := witnessFrom oriented (initialZ false) 20104 48572 [(9,229)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 20104 (-80) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented true false table cert 20104 (-80) checkedCert m hm
#print axioms never
end C0REM1730

namespace C0REM1736
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial true false table
def cert : Certificate := witnessFrom oriented (initialZ false) 19128 46006 [(9,229)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 19128 (-80) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented true false table cert 19128 (-80) checkedCert m hm
#print axioms never
end C0REM1736

namespace C1REM390
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 23992 19302 [(2,42), (133,143)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 23992 (-132) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 23992 (-132) checkedCert m hm
#print axioms never
end C1REM390

namespace C1REM1179
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,3⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨false,true,1⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 23992 19302 [(2,42), (133,143)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 23992 (-132) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 23992 (-132) checkedCert m hm
#print axioms never
end C1REM1179

namespace C0REM627
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,3⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial true false table
def cert : Certificate := witnessFrom oriented (initialZ false) 135300 19958 [(9,33), (688,760)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 135300 (-1004) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented true false table cert 135300 (-1004) checkedCert m hm
#print axioms never
end C0REM627

namespace C0REM1403
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial true false table
def cert : Certificate := witnessFrom oriented (initialZ false) 133274 19728 [(9,33), (688,760)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 133274 (-1004) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented true false table cert 133274 (-1004) checkedCert m hm
#print axioms never
end C0REM1403

namespace C0RDM154
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial false false table
def cert : Certificate := witnessFrom oriented (initialZ false) 132476 12262 [(73,81), (489,513)]
theorem checkedCert : checkedFrom oriented cert (initialZ false) 132476 (-480) := by decide +kernel
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_oriented false false table cert 132476 (-480) checkedCert m hm
#print axioms never
end C0RDM154

end BB6Coverage.Agent19Raw40LateCrossing
