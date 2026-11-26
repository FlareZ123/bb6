import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120OneLBLiteral.M502
open BB6Coverage BB6Coverage.Agent31Pump
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none

def preWord : List Bool := [true,false,false,false,false,false,false,false]
def block : List Bool := [false,false,true,true,true,true]
def sufWord : List Bool := [true,true,true,true]
def family (n : Nat) : Z0 := ⟨1,[],preWord ++ rep block n ++ sufWord⟩
theorem entry : run0 table 194 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem frame (tail : List Bool) :
    run0 table 458 ⟨1,[],preWord ++ tail⟩ = some ⟨1,[],preWord ++ block ++ tail⟩ := by rfl
theorem growth (n : Nat) : run0 table 458 (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using frame (rep block n ++ sufWord)
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 194 (fun _ => 458) entry (by intro k; decide) growth m hm
#print axioms frame
#print axioms never
end BB6.Agent3Raw120OneLBLiteral.M502
