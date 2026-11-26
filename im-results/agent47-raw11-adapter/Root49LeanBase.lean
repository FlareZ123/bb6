import PhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Root49
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | _,_ => none)
end BB6.Agent47Root49
