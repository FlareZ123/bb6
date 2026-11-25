import SweepPumping

namespace BB6Coverage.Agent4Raw109LF1475
open Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none

def P : List Bool := [false,false,false,true,true,false,true,true,true,false,true,true,false,false]
def I : List Bool := [true,false,false,true,true,true,true,true,true,true,true,true,true,true]
def F (L : List Bool) : Z0 := ⟨1,P++L,[false]⟩

theorem epoch (L : List Bool) : run0 table 532 (F L) = some (F (I++L)) := by rfl

theorem entry : run0 table 643 ⟨0,[],[]⟩ = some (F I) := by rfl

def family (n : Nat) : Z0 := F (rep I (n+1))

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 643 (fun _ => 532) entry (fun _ => by decide)
    (fun n => epoch (rep I (n+1))) m hm
#print axioms never
end BB6Coverage.Agent4Raw109LF1475
