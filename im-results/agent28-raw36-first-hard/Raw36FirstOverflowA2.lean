import Agent46AutoPump
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.Auto.Raw36FirstOverflowA2
open BB6Coverage Agent31Pump Auto

/-! One exact source-level two-counter overflow lemma. The F0 hole is never
    traversed, and no assumption about a completed transition is needed. -/
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,0⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨false,false,3⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none

/-- Odd u=2n+1, leftmost 0 scanned in state A, v=2. -/
def source : PZ := ⟨0, .lit [],
  .periodic [false,true,true,true,false,true] [false,true,false,true] (.lit [false,true,true,true,false,true,false,true,false,false])⟩

/-- After the reset, state B at the new left frontier with
    parameters u'=13, v'=u+2=2n+3. -/
def target : PZ := ⟨1, .lit [],
  .periodic [true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,true,false,true,false,true,false,true] [false,true,false,true] (.lit [false,false])⟩

def ops : List Action :=
  List.replicate 1 Action.step
  ++ [.right [false] [true,true,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [false,true,true,true,false,true,false,true,false,false]) 10]
  ++ List.replicate 19 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,true,false,false]) 8]
  ++ List.replicate 27 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,true,false,false]) 10]
  ++ List.replicate 29 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,true,false,false]) 8]
  ++ List.replicate 35 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,true,false,false]) 10]
  ++ List.replicate 39 Action.step
  ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [false,true,false,true] (.lit [true]) (.lit [true,false]) 8]
  ++ List.replicate 43 Action.step
  ++ [.right [false] [true,true,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true] [false,true,false,true] [true,true,true,true] (.lit [true]) (.lit [true,false]) 10]
  ++ List.replicate 49 Action.step
  ++ [.left [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true] [true,false,true,false] (.lit [true]) (.lit [false]) 8]
  ++ List.replicate 490 Action.step

def accepted : Bool :=
  match Auto.traceRun p ops source with
  | none => false
  | some out => decide (out.a=72 ∧ out.b=732 ∧ out.z.norm=target.norm)

theorem checked : accepted = true := by decide

/-- Arbitrarily long, exact F0-safe phase reset, uniformly in n. -/
theorem transport (n : Nat) :
    run0 p (72*n+732) (source.eval n) = some (target.eval n) := by
  cases hr : Auto.traceRun p ops source with
  | none =>
    have hh := checked
    simp [accepted,hr] at hh
  | some out =>
    have hh : out.a=72 ∧ out.b=732 ∧ out.z.norm=target.norm := by
      simpa [accepted,hr] using checked
    have hs := Auto.traceRun_sound p ops hr n
    have hn := congrArg (fun z : PZ => z.eval n) hh.2.2
    rw [PZ.norm_sound,PZ.norm_sound] at hn
    rw [hh.1,hh.2.1,hn] at hs
    exact hs

#print axioms checked
#print axioms transport
end BB6Coverage.Agent31Pump.Auto.Raw36FirstOverflowA2
