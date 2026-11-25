import BiDFA
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent40Raw118CrossBank.M3970
open BB6Coverage BB6Coverage.Agent16BiDFA

def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0, false => some (some ⟨true, true, 1⟩)
  | 1, false => some (some ⟨true, true, 2⟩)
  | 1, true => some (some ⟨false, true, 0⟩)
  | 2, false => some (some ⟨false, true, 3⟩)
  | 2, true => some (some ⟨true, true, 1⟩)
  | 3, false => some (some ⟨true, false, 3⟩)
  | 3, true => some (some ⟨true, true, 4⟩)
  | 4, false => some (some ⟨true, false, 5⟩)
  | 4, true => some (some ⟨false, false, 4⟩)
  | 5, false => some (some ⟨false, true, 1⟩)
  | 5, true => some (some ⟨false, false, 4⟩)
  | _, _ => none

def cert : Cert := ⟨[0,1,2,3,4,5,6,4,7,8,0,0,9,2,0,3,10,9,5,3,11,5,0,0], [1,2,3,4,5,6,7,4,8,9,8,4,10,2,8,2,11,1,4,3,4,6,9,10],
  [⟨0,false,0⟩,⟨1,true,0⟩,⟨2,true,6⟩,⟨3,true,1⟩,⟨3,true,9⟩,⟨4,true,3⟩,⟨6,false,3⟩,⟨8,true,4⟩,⟨9,true,8⟩],
  [⟨0,false,0⟩,⟨1,true,8⟩,⟨2,true,0⟩,⟨3,false,1⟩,⟨4,false,9⟩,⟨4,false,10⟩,⟨4,true,3⟩,⟨4,true,5⟩,⟨5,false,2⟩,⟨6,true,2⟩,⟨6,true,10⟩,⟨8,false,4⟩,⟨8,false,5⟩,⟨9,false,11⟩,⟨10,true,11⟩,⟨11,false,8⟩],
  [⟨0,false,0,0⟩,⟨0,false,0,8⟩,⟨1,false,1,0⟩,⟨1,false,1,4⟩,⟨1,false,1,5⟩,⟨1,false,4,1⟩,⟨1,false,4,2⟩,⟨1,false,9,0⟩,⟨1,false,9,4⟩,⟨1,false,9,5⟩,⟨1,true,0,11⟩,⟨2,false,3,0⟩,⟨2,false,3,2⟩,⟨2,false,3,9⟩,⟨2,false,3,10⟩,⟨2,true,3,3⟩,⟨2,true,3,5⟩,⟨2,true,8,0⟩,⟨2,true,8,8⟩,⟨3,false,3,2⟩,⟨3,false,3,10⟩,⟨3,false,6,0⟩,⟨3,false,6,11⟩,⟨3,true,1,6⟩,⟨3,true,6,0⟩,⟨3,true,6,11⟩,⟨3,true,9,6⟩,⟨4,false,0,11⟩,⟨4,false,2,0⟩,⟨4,false,2,8⟩,⟨4,false,3,3⟩,⟨4,false,3,5⟩,⟨4,true,0,8⟩,⟨4,true,1,4⟩,⟨4,true,1,5⟩,⟨4,true,3,2⟩,⟨4,true,3,9⟩,⟨4,true,3,10⟩,⟨4,true,4,11⟩,⟨4,true,8,8⟩,⟨4,true,9,4⟩,⟨4,true,9,5⟩,⟨5,false,0,10⟩,⟨5,true,1,4⟩,⟨5,true,6,1⟩,⟨5,true,6,2⟩,⟨5,true,9,4⟩]⟩

theorem checked : check table cert = true := by decide

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6Coverage.Agent16BiDFA.never table cert checked m hm

#print axioms never
end BB6Coverage.Agent40Raw118CrossBank.M3970
