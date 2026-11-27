import Agent28OpenRightSweep
import Raw36FirstOverflowA2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstDescentB
open BB6Coverage Agent31Pump Auto

def p : PartialMachine := Raw36FirstOverflowA2.p

/-- B-side descent for odd u=2*n+3, and arbitrary protected right tail. -/
def source : PZ := ⟨1,.lit [],
  .periodic [true,false,true,false,true] [false,true,false,true] (.lit [false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true])⟩

def target : PZ := ⟨1,.lit [],
  .periodic [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] (.lit [false,true,true,true])⟩

def ops : List Action :=
  List.replicate 6 Action.step
  ++ [.right [false] [true,true,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 19 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 27 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 29 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 35 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 39 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 43 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 49 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 51 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 59 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 59 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 69 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 67 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 79 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true]) 8]
  ++ List.replicate 75 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,true]) 10]
  ++ List.replicate 89 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true]) 8]
  ++ List.replicate 83 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true]) 10]
  ++ List.replicate 99 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true]) 8]
  ++ List.replicate 91 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true]) 10]
  ++ List.replicate 109 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true]) 8]
  ++ List.replicate 93 Action.step

def accepted : Bool :=
  match OpenRight.traceRun p ops source with
  | none => false
  | some out => decide (out.a=180 ∧ out.b=1270 ∧ out.z.norm=target.norm)

theorem checked : accepted = true := by decide

theorem transport (n : Nat) (tail : List Bool) :
    run0 p (180*n+1270) ((OpenRight.attachZ source tail).eval n) =
    some ((OpenRight.attachZ target tail).eval n) := by
  cases hr : OpenRight.traceRun p ops source with
  | none =>
    have hh := checked
    simp [accepted,hr] at hh
  | some out =>
    have hh : out.a=180 ∧ out.b=1270 ∧ out.z.norm=target.norm := by
      simpa [accepted,hr] using checked
    have hs := OpenRight.traceRun_sound p ops hr n tail
    have hn := congrArg (fun z : PZ => (OpenRight.attachZ z tail).eval n) hh.2.2
    rw [OpenRight.norm_attachZ_eval,OpenRight.norm_attachZ_eval] at hn
    rw [hh.1,hh.2.1,hn] at hs
    exact hs

#print axioms checked
#print axioms transport
end BB6Coverage.Agent31Pump.Auto.Raw36FirstDescentB
