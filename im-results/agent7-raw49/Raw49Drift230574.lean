import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Drift230574
open BB6Coverage BB6Coverage.Agent31Pump

/-- Raw49/C23 open leaf 574; F1 is unspecified. -/
def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,5⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨true,false,0⟩)
  | 5,false => some (some ⟨false,true,0⟩)
  | _,_ => none

def pre : List Bool := [false,false,true,true,false,true,true,true,false,true,true,false,true,true,true,true,true,true,false]
def block : List Bool := [false,true,true,true,true,true,true,false,false,true,true,true,true]
def tail : List Bool := [false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true]

/-- The entire 337-step return reads only the fixed prefix and the fresh
    right frontier. It inserts one 13-bit word before an opaque left tail. -/
theorem one (L : List Bool) :
    run0 table 337 ⟨3,pre++L,[]⟩ = some ⟨3,pre++block++L,[]⟩ := by rfl

def family (n : Nat) : Z0 := ⟨3,pre++(rep block n++tail),[]⟩

theorem growth (n : Nat) :
    run0 table 337 (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using one (rep block n++tail)

theorem entry0 : run0 table 180 ⟨0,[],[]⟩ = some ⟨2,[true,false,false,false,true,true,true,true,true,true,true,true],[false,true,true,true]⟩ := by rfl

theorem entry1 : run0 table 180 ⟨2,[true,false,false,false,true,true,true,true,true,true,true,true],[false,true,true,true]⟩ = some ⟨5,[false,true,true],[true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true]⟩ := by rfl

theorem entry2 : run0 table 180 ⟨5,[false,true,true],[true,false,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true]⟩ = some ⟨0,[true,false,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[true,false,true,false,false,true,true,true,true,false,false,true,true,true]⟩ := by rfl

theorem entry3 : run0 table 180 ⟨0,[true,false,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[true,false,true,false,false,true,true,true,true,false,false,true,true,true]⟩ = some ⟨2,[true,true,true,true,false,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[true,false,false,true,true,true,true,true,true,true,false,false,true,true,true]⟩ := by rfl

theorem entry4 : run0 table 180 ⟨2,[true,true,true,true,false,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[true,false,false,true,true,true,true,true,true,true,false,false,true,true,true]⟩ = some ⟨2,[false,false,false,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[]⟩ := by rfl

theorem entry5 : run0 table 180 ⟨2,[false,false,false,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[]⟩ = some ⟨0,[true,true,false,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true]⟩ := by rfl

theorem entry6 : run0 table 180 ⟨0,[true,true,false,true,true,true,true,false,true,true,true,true,true,false,true,true,true,true,true,true,true,false,true,true,true,false,true,true,false,false,true,true,false,true,true],[true,false,true,true,true,true,false,false,true,true,true,true,true,true,true,false,false,true,true,true]⟩ = some ⟨3,[false,false,false,false,true,true,true,false,true,true,true,false,false,false,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true],[true,true,true,true,true,true,true,false,false,true,true,true]⟩ := by rfl

theorem entry7 : run0 table 180 ⟨3,[false,false,false,false,true,true,true,false,true,true,true,false,false,false,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true],[true,true,true,true,true,true,true,false,false,true,true,true]⟩ = some ⟨3,[false,false,true,false,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true],[false,true,true,true,true,false,true,false,false,true,true,true]⟩ := by rfl

theorem entry8 : run0 table 90 ⟨3,[false,false,true,false,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true],[false,true,true,true,true,false,true,false,false,true,true,true]⟩ = some ⟨3,[false,false,true,true,false,true,true,true,false,true,true,false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,true,true,false,false,true,true,true,true,false,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true],[]⟩ := by rfl

theorem entry : run0 table 1530 ⟨0,[],[]⟩ = some (family 0) := by
  exact join0 (join0 (join0 (join0 (join0 (join0 (join0 (join0 (entry0) entry1) entry2) entry3) entry4) entry5) entry6) entry7) entry8

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 1530 (fun _ => 337) entry (by intro n; decide) growth m hm

#print axioms never
end BB6.Agent7Raw49Drift230574
