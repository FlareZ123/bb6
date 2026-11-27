import Raw36FirstOverflowA2
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstOverflowB3
open BB6Coverage Agent31Pump Auto

def p : PartialMachine := Raw36FirstOverflowA2.p
/-- B counter reset at residue 3, source u=2*n+3. -/
def source : PZ := ⟨1,.lit [],
  .periodic [true,false,true,false,true] [false,true,false,true] (.lit [false,true,true,true,false,true,false,true,false,true,false,false])⟩

/-- Target A(7,2*n+7); the F0 hole is never read. -/
def target : PZ := ⟨0,.lit [],
  .periodic [false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] (.lit [false,false])⟩

def ops : List Action :=
  List.replicate 6 Action.step
  ++ [.right [false] [true,true,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [false,true,true,true,false,true,false,true,false,true,false,false]) 10]
  ++ List.replicate 19 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,false]) 8]
  ++ List.replicate 27 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,true,false,false]) 10]
  ++ List.replicate 29 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,false]) 8]
  ++ List.replicate 35 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,false]) 10]
  ++ List.replicate 39 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,false]) 8]
  ++ List.replicate 43 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,false]) 10]
  ++ List.replicate 49 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,false]) 8]
  ++ List.replicate 51 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,false]) 10]
  ++ List.replicate 59 Action.step
  ++ [.left [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [true,false,true,false] (.lit [true]) (.lit [false]) 8]
  ++ List.replicate 285 Action.step

def accepted : Bool :=
  match Auto.traceRun p ops source with
  | none => false
  | some out => decide (out.a=90 ∧ out.b=642 ∧ out.z.norm=target.norm)

theorem checked : accepted = true := by decide

theorem transport (n : Nat) :
    run0 p (90*n+642) (source.eval n) =
    some (target.eval n) := by
  cases hr : Auto.traceRun p ops source with
  | none =>
    have hh := checked
    simp [accepted,hr] at hh
  | some out =>
    have hh : out.a=90 ∧ out.b=642 ∧ out.z.norm=target.norm := by
      simpa [accepted,hr] using checked
    have hs := Auto.traceRun_sound p ops hr n
    have hn := congrArg (fun z : PZ => z.eval n) hh.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [hh.1,hh.2.1,hn] at hs
    exact hs

#print axioms checked
#print axioms transport
end BB6Coverage.Agent31Pump.Auto.Raw36FirstOverflowB3
