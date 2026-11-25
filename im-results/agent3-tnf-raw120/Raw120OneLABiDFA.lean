import BiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120OneLABiDFA
open BB6Coverage BB6Coverage.Agent16BiDFA
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,0⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,false => some (some ⟨false,true,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none
def cert : Cert := ⟨[0,1,2,3,4,5,6,6,2,1,2,1,5,0],[0,1,2,3,1,1,1,2],
  [⟨0,false,0⟩,⟨1,true,0⟩,⟨1,true,5⟩,⟨2,false,1⟩,⟨2,false,4⟩,⟨2,false,5⟩,⟨3,true,1⟩,⟨4,false,2⟩,⟨5,true,2⟩,⟨6,false,3⟩],
  [⟨0,false,0⟩,⟨1,true,0⟩,⟨1,true,2⟩,⟨1,false,3⟩,⟨1,false,2⟩,⟨2,true,3⟩,⟨3,true,1⟩],
  [⟨0,false,0,0⟩,⟨1,false,1,0⟩,⟨2,false,3,0⟩,⟨3,false,6,0⟩,⟨3,false,3,1⟩,⟨3,true,1,3⟩,⟨4,true,3,1⟩,⟨4,true,1,3⟩,⟨4,true,0,2⟩,⟨4,false,0,1⟩,⟨0,false,0,3⟩,⟨1,true,1,1⟩,⟨5,true,2,0⟩,⟨5,true,2,2⟩,⟨0,false,5,0⟩,⟨0,true,5,3⟩,⟨4,true,5,2⟩,⟨5,false,2,3⟩,⟨4,true,2,1⟩,⟨1,true,4,1⟩,⟨4,false,1,3⟩,⟨4,false,4,3⟩,⟨0,true,0,2⟩,⟨0,true,5,2⟩,⟨0,false,2,2⟩,⟨5,false,2,2⟩,⟨1,true,5,3⟩,⟨1,true,4,3⟩,⟨4,false,5,3⟩,⟨5,true,2,1⟩,⟨0,true,2,2⟩,⟨0,true,5,0⟩,⟨0,false,5,3⟩,⟨0,false,5,2⟩,⟨4,false,1,1⟩,⟨4,false,4,1⟩,⟨4,false,5,1⟩,⟨4,true,2,0⟩,⟨1,true,1,3⟩,⟨0,true,0,3⟩,⟨0,false,2,3⟩,⟨0,true,2,3⟩,⟨1,true,5,1⟩]⟩
theorem checked : check table cert = true := by decide
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Agent16BiDFA.never table cert checked m hm
#print axioms never
end BB6.Agent3Raw120OneLABiDFA
