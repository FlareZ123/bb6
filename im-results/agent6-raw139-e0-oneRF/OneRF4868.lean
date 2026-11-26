import PadGrowth
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent6E0OneRF4868
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,4⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨true,true,0⟩)
  | _,_ => none

def P : List Bool := [false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false]
def B : List Bool := [false, false, false, false, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, false, false, false, true, true, true, true]
def T : List Bool := [false, false, false, false, false, false, true, true, true, true, false, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, false, false, false, false, true, true, true, true]
def C (tail : List Bool) : Z0 := ⟨5,P++tail,[]⟩
def family (k : Nat) := C (rep B k ++ T)

theorem pump (tail : List Bool) : run0 p 827 (C tail) = some (C (B++tail)) := rfl

theorem seed : Reach p 953 ⟨0,[],[]⟩ (family 0) := exactRun (by decide +kernel)

theorem growth (k : Nat) : Reach p 827 (family k) (family (k+1)) := by
  have h := pump (rep B k ++ T)
  exact exactRun (by simpa only [family,rep,List.append_assoc] using h)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_pad_growth p family 953 (fun _ => 827) seed (by intro k; decide) growth m hm
#print axioms pump
#print axioms growth
#print axioms never
end BB6.Agent6E0OneRF4868
