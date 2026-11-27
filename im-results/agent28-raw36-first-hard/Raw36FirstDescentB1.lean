import Agent28OpenRightSweep
import Raw36FirstOverflowA2

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstDescentB1
open BB6Coverage Agent31Pump Auto

def p : PartialMachine := Raw36FirstOverflowA2.p

/-- The single odd first-counter value u=1 left out by the B(u≥3) uniform
    sweep proof; arbitrary suffix remains protected. -/
def source : PZ := ⟨1,.lit [],
  .lit [true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true]⟩
def target : PZ := ⟨1,.lit [],
  .lit [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true]⟩

def ops : List Action := List.replicate 1090 Action.step

def accepted : Bool :=
  match OpenRight.traceRun p ops source with
  | none => false
  | some out => decide (out.a=0 ∧ out.b=1090 ∧ out.z.norm=target.norm)

theorem checked : accepted = true := by decide

/-- B(1,v) → B(21,v-10), v≥10, in exactly 1090 steps, for every
    concrete arbitrary suffix. -/
theorem transport (tail : List Bool) :
    run0 p 1090 ((OpenRight.attachZ source tail).eval 0) =
    some ((OpenRight.attachZ target tail).eval 0) := by
  cases hr : OpenRight.traceRun p ops source with
  | none =>
    have hh := checked
    simp [accepted,hr] at hh
  | some out =>
    have hh : out.a=0 ∧ out.b=1090 ∧ out.z.norm=target.norm := by
      simpa [accepted,hr] using checked
    have hs := OpenRight.traceRun_sound p ops hr 0 tail
    have hn := congrArg (fun z : PZ => (OpenRight.attachZ z tail).eval 0) hh.2.2
    rw [OpenRight.norm_attachZ_eval,OpenRight.norm_attachZ_eval] at hn
    rw [hh.1,hh.2.1,hn] at hs
    simpa using hs

#print axioms checked
#print axioms transport
end BB6Coverage.Agent31Pump.Auto.Raw36FirstDescentB1
