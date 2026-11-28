import Agent5TailPump
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-
Exact 60-cell left-moving glider for Raw11 q0-151 remaining leaf 23.
Source table: 1RB1LC_1RC0LF_0LA1RD_0RC0RE_1LF---_0LB1LB.
At 9181 primitive steps from blank: q=B, left stack [], right stack
prefixWord ++ initialTail; every arbitrary right suffix is preserved by a
4174-step return which prepends a 60-cell block to that suffix.
This is an original-source parametric recurrence, not a sampled 3M-step run.
-/
namespace BB6Coverage.Agent31Pump.Raw11Q0LeftGlider151
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay Tails

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,5⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨false,true,2⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => none
  | 5,false => some (some ⟨false,false,1⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none

def prefixWord : List Bool := [true,false,true,false,true,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,true,false,true,false,true,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,true,false,true,false,true,false,false,false,true,false,false,false,true,false,true,false,false,false,false,false,false,false,false,false,true,false,false,false]
def block : List Bool := [false,false,true,false,true,false,false,true,false,false,false,false,false,true,false,true,false,false,true,false,false,false,false,false,true,false,true,false,true,false,false,false,true,false,true,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,false,true,false,false,false,true,false,false,false]
def initialTail : List Bool := [true,false,false,false,false,false,true,false,false,false,true,false,true,false,false,true,false,false,false,false,false,false,false,true,false,true,false,false,false,false,false,true,false,true,false,true,false,false,true,false,false,false,true,false,true,false,false,true,false,false,true,false,false,false,true,false,false,false,true,false,false,false,true,false,true,false,false,true,false,false,false,false,false,true,false,true,false,false,true]
def config (X : List Bool) : Z0 := ⟨1,[],prefixWord ++ X⟩

def cert : Tails.Cert :=
  ⟨⟨1,.lit [],.tail prefixWord false⟩,
    ⟨1,.lit [],.tail (prefixWord ++ block) false⟩,
    [.steps 4174],0,0,4174⟩
theorem check_cert : Tails.check table cert = true := by decide +kernel

theorem repeat_step (X : List Bool) :
    run0 table 4174 (config X) = some (config (block ++ X)) := by
  simpa [config,cert,Tails.PZ.eval,Tails.Word.eval,List.append_assoc] using
    Tails.check_sound table cert check_cert 0 0 X []

theorem seed : run0 table 9181 ⟨0,[],[]⟩ = some (config initialTail) := by decide +kernel

def region (s : Z0) : Prop := ∃ X, s = config X
theorem closed (s : Z0) (h : region s) :
    ∃ k t, 0 < k ∧ region t ∧ run0 table k s = some t := by
  obtain ⟨X,rfl⟩ := h
  exact ⟨4174, config (block ++ X),by decide,⟨_,rfl⟩,repeat_step X⟩

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Multi.never_of_region table region 9181 (config initialTail) seed ⟨_,rfl⟩ closed m hm

theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)

#print axioms cover
end BB6Coverage.Agent31Pump.Raw11Q0LeftGlider151
