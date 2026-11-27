
import Agent46AutoPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Auto.Raw36Counter2
open BB6Coverage Agent31Pump Auto

/-! Exact nonhalting certificate for
    1RB0LB_1RC0LA_0RD1RE_0LD1LB_0RF---_1LD0RA.
    The E1 hole is never queried by the parametric return. -/

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨true,false,3⟩)
  | 5,true => some (some ⟨false,true,0⟩)
  | _,_ => none

/-- D scanning the rightmost zero of (11100)^(n+3) 1100. -/
def family : PZ := ⟨3,
  .periodic [false,false,true,true,
             false,false,true,true,true,
             false,false,true,true,true,
             false,false,true,true,true]
            [false,false,true,true,true] (.lit []),
  .lit []⟩

/-- Eight source-sound whole-block sweeps and 854 literal steps
    with affine aggregate time 84*n+854 and 6-block growth. -/
def ops : List Action :=
  List.replicate 18 Action.step
  ++ [.left [] [true,true,true,false,false,true,true,true,false,false,true,true,true] [false,false,true,true,true] [false,false,true,false,true] (.lit [true,false,false,true,false,true]) (.lit []) 19]
  ++ List.replicate 326 Action.step
  ++ [.right [false] [true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [false,false,true,false,true] [true,false,false,true,true] (.lit [true]) (.lit [true,false,false,true,false,true]) 5]
  ++ List.replicate 29 Action.step
  ++ [.left [false] [true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [true,false,false,true,true] [false,false,true,false,true] (.lit [false,true,false,true]) (.lit [true]) 15]
  ++ List.replicate 104 Action.step
  ++ [.right [false] [true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [false,false,true,false,true] [true,false,false,true,true] (.lit [true]) (.lit [false,true,false,true]) 5]
  ++ List.replicate 35 Action.step
  ++ [.left [] [true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [true,false,false,true,true] [false,false,true,false,true] (.lit [false,true]) (.lit [true]) 15]
  ++ List.replicate 120 Action.step
  ++ [.right [false] [true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [false,false,true,false,true] [true,false,false,true,true] (.lit [true]) (.lit [false,true]) 5]
  ++ List.replicate 40 Action.step
  ++ [.left [] [true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true,true,false,false,true,true] [true,false,false,true,true] [false,false,true,false,true] (.lit []) (.lit [true]) 15]
  ++ List.replicate 135 Action.step
  ++ [.right [false] [true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true,false,false,true,false,true] [false,false,true,false,true] [true,false,false,true,true] (.lit [true]) (.lit []) 5]
  ++ List.replicate 47 Action.step

/-- The blank entry at 132 steps is included in the checked certificate. -/
def cert : Cert := ⟨132,family,6,ops,84,854⟩

theorem checked : Auto.check p cert = true := by decide

theorem return (n : Nat) :
    run0 p (84*n+854) (family.eval n) =
      some (family.eval (n+6)) := by
  simpa [Nat.add_comm] using Auto.check_growth p cert checked n

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  Auto.check_never p cert checked m hm

#print axioms checked
#print axioms never
end BB6Coverage.Agent31Pump.Auto.Raw36Counter2
