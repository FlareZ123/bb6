import Raw40OrientedCrossing
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
open BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper
def table : PartialMachine := fun slot => match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
def oriented : PartialMachine := orientPartial true true table

end BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
