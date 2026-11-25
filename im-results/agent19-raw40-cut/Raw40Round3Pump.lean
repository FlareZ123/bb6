import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Round3.Leaf4
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
-- 1RB0LB1RC0RC0RD0LE1LD1LA1LC0LF1LA---
def table : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | 4,false => some (some ⟨true,false,2⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | 5,false => some (some ⟨true,false,0⟩)
  | _,_ => none

def cert : Cert := ⟨297, ⟨0, .lit [false], .periodic [true] [false,true,false,true,false,true] (.lit [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false])⟩, 1,
  [.right [false] [true] [false,true,false,true,false,true] [false,true,false,true,false,true] (.lit []) (.lit [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false]) 12] ++ List.replicate 57 Action.step ++ [.left [true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [true] [false,true,false,true,false,true] [false,true,false,true,false,true] (.lit []) (.lit [true]) 42] ++ List.replicate 173 Action.step ++ [.right [true,false] [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true,false,true] [false,true,false,true,false,true] (.lit []) (.lit [true]) 12] ++ List.replicate 59 Action.step ++ [.left [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [] [false,true,false,true,false,true] [true,false,true,false,true,false] (.lit []) (.lit []) 6] ++ List.replicate 34 Action.step, 72, 323⟩

theorem checked : check table cert = true := by decide +kernel

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  check_never table cert checked m hm

#print axioms checked
#print axioms never
end BB6.Agent19Raw40.Round3.Leaf4
