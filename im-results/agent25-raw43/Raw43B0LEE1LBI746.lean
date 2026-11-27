import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43B0LEE1LBI746
open BB6Coverage BB6Coverage.Agent31Pump

def table : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,0⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,1⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | 4,true => some (some ⟨true,false,3⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | 5,true => none
  | _,_ => none

def R0 : List Bool := [
  true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,
  false,true,false,true,false,true,false,false,true,false,false,true,false,true,true,false,
  true,false,true,true,false,true,false,false,true,false,true,false,false,true,false,false,
  true,false,true,false,true,false,false,true,false,false,false,true,false,false,true,false,
  true,false,false,true,false,true]

def family (k : Nat) : Z0 := ⟨3, [], rep [true] k ++ R0⟩
def cost (_ : Nat) : Nat := 1

theorem first :
    run0 table 1983 ⟨0,[],[]⟩ = some (family 0) := by
  decide

theorem positive (k : Nat) : 0 < cost k := by simp [cost]

theorem growth (k : Nat) :
    run0 table (cost k) (family k) = some (family (k+1)) := by
  simp [cost, family, rep, run0, step0, table, move0]

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1983 cost first positive growth m hm

#print axioms first
#print axioms growth
#print axioms never
end BB6.Agent25Raw43B0LEE1LBI746
