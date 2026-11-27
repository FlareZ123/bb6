import Agent5TailPump
import Agent5MultiPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6Coverage.Agent31Pump.Raw11Q0Linear151
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay Tails

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => none
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨false,true,4⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨true,true,0⟩)
  | 4,true => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,2⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none

def prefixWord : List Bool := [false,true,true,true,false,true,false,false,false,true,true,true]
def block : List Bool := [false,true,true,true]
def initialTail : List Bool := [false,true,false,false,false,true,true,true,false,true,true,true,true,false,false,false,true,false,false,false,true,true,true,false,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true,false,false,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,false,false,false,true,false,false,false,true,true,true,false,true,true,true,false,true,true,true]
def config (X : List Bool) : Z0 := ⟨2,prefixWord ++ X,[]⟩
def cert : Tails.Cert :=
  ⟨⟨2,.tail prefixWord false,.lit []⟩,
    ⟨2,.tail (prefixWord ++ block) false,.lit []⟩,[.steps 26],0,0,26⟩
theorem check_cert : Tails.check table cert = true := by decide +kernel
theorem repeat_step (X : List Bool) :
    run0 table 26 (config X) = some (config (block ++ X)) := by
  simpa [config,cert,Tails.PZ.eval,Tails.Word.eval,List.append_assoc] using
    Tails.check_sound table cert check_cert 0 0 X []
theorem seed : run0 table 4866 ⟨0,[],[]⟩ = some (config initialTail) := by decide +kernel
def region (s : Z0) : Prop := ∃ X, s = config X
theorem closed (s : Z0) (h : region s) :
    ∃ k t, 0 < k ∧ region t ∧ run0 table k s = some t := by
  obtain ⟨X,rfl⟩ := h
  exact ⟨26,config (block ++ X),by decide,⟨_,rfl⟩,repeat_step X⟩
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  Multi.never_of_region table region 4866 (config initialTail) seed ⟨_,rfl⟩ closed m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end BB6Coverage.Agent31Pump.Raw11Q0Linear151
