import SweepPumping
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw391LEDriftPair
open BB6Coverage BB6Coverage.Agent31Pump
inductive V where | a | b deriving DecidableEq, Repr
-- a=21614, b=21623. F0 is undefined.
def table (v : V) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨v = .b,true,5⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | 5,true => some (some (if v = .a then ⟨false,false,4⟩ else ⟨true,true,1⟩))
  | _,_ => none

def entry (v : V) : Nat := if v = .a then 1154 else 1124
def period (v : V) : Nat := if v = .a then 2158 else 2108
def P : List Bool := [false,false,false,false,false,false,false,false,true,true,false,true,true,false,false,true,true,false,true,true,false,false,false,false,false,false]
def I : List Bool := [false,false,true,true,false,true,true,true,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true]
def T : List Bool := [true,true,false,false,false,false,true,false,false,true,true,true,true,false,false,true,true]
theorem first (v : V) : run0 (table v) (entry v) ⟨0,[],[]⟩ = some ⟨4,[],P++T⟩ := by
  cases v <;> rfl

theorem drift (v : V) (R : List Bool) :
    run0 (table v) (period v) ⟨4,[],P++R⟩ = some ⟨4,[],P++I++R⟩ := by
  cases v <;> rfl

def family (n : Nat) : Z0 := ⟨4,[],P++rep I n++T⟩

theorem never (v : V) (m : Machine) (hm : compatible (table v) m) : NeverHalts m := by
  apply never_of_growth (table v) family (entry v) (fun _ => period v) _ _ _ m hm
  · exact first v
  · intro n; cases v <;> decide
  · intro n
    simpa only [family,rep,List.append_assoc] using drift v (rep I n++T)

#print axioms drift
#print axioms never
end BB6.Agent11Raw391LEDriftPair
