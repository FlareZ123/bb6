import Raw58Live
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent7LF11181
open BB6Coverage Agent31Pump
-- 1RB1LF_1RC0LB_0RD1RA_1LD1RE_---0RA_1LB0RF
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,5⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,0⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,4⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none
def P : List Bool := [false,false,false,false,false,false,false,false,true,true,true,true,false,true,true,true,true,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true]
def W : List Bool := [true,true,true,false,true,true,false,false]
def T : List Bool := [true,true,true,false,true,true,false,false,false,true,true,false,false,false,false,false,false,true,true,true,true,true,true,false,false,false,false,false,false,false,true,true,true,true,true,true,false,true,true,true,true,true,false,false,false,false,false,true,true,true,true,true,false,false,false,false,true,true,true,true,true,true,false,false,true,true,true,true,true,false,false,false,false,false,false,true,true,true,true,false,true,true,false,false,true,true]

def family (k : Nat) : Z0 := ⟨1,[],P++rep W k++T⟩

theorem pump (R : List Bool) :
    run0 table 1226 ⟨1,[],P++R⟩ = some ⟨1,[],P++W++R⟩ := by rfl

theorem growth (k : Nat) : run0 table 1226 (family k) = some (family (k+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep W k++T)

theorem entry : run0 table 11883 ⟨0,[],[]⟩ = some (family 0) := by
  rfl

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 11883 (fun _ => 1226) entry (by intro; decide) growth m hm

#print axioms pump
#print axioms entry
#print axioms growth
#print axioms never
end BB6Coverage.Agent7LF11181
