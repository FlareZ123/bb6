import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw13Coupled6RBDrifts
open BB6Coverage Agent31Pump Auto

/-- 1RB1LD1RC1RB1LA1RE0LF0LA1LF0RB---0LC -/
def p0 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,5⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def c0 : Cert := ⟨2609,⟨0,(.lit []),(.periodic [false,true,false,true,true,false,true,true,true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,false,true,false,true,false,true,true,false,true,false,true] [false,true,false,true,false,true,true,false,true,true,true] (.lit [false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,true,true,true]))⟩,1,(List.replicate 333 .step),0,333⟩
theorem checked0 : check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m := check_never p0 c0 checked0 m hm
#print axioms never0

/-- 1RB1LD1RC1RB1LA1RE1LF0LA0RA0RB---0LC -/
def p1 : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,5⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | 4,false => some (some ⟨false,true,0⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none
def c1 : Cert := ⟨6132,⟨0,(.lit []),(.periodic [true,false,true,true,true,true,true,false,true,false,true,true,false,true,true,true,true,true,true,true,true,false,true,false,true,false,true,true,false,true,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,true,true,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,true,true,true,true,true,true,false,true,false,true,false] [true,false,true,true,false,true,true,true,true,true,true,true,false] (.lit [true,false,true,true,false,true,true,true,true,false,true,false,true,false,true,false,true,false,true,true]))⟩,1,(List.replicate 1259 .step),0,1259⟩
theorem checked1 : check p1 c1 = true := by decide
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m := check_never p1 c1 checked1 m hm
#print axioms never1
end BB6Coverage.Agent31Pump.Auto.Raw13Coupled6RBDrifts
