import Agent5TailPump
import Root56Coverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6Coverage.Agent31Pump.Raw11Q0Sweep150
open BB6Coverage Agent31Pump BB6.Agent13BlankDelay Tails

def table : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,1⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,3⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => none
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none

def cert : Tails.Cert := ⟨⟨0,(.lit []),(.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.lit []))⟩,⟨0,(.lit []),(.periodic [false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] false (.lit []))⟩,
  [.steps 3,
   .right [true] [true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] [true,true,true] [true,true,false] false (.lit [true]) (.lit []) 3,
   .steps 78,
   .left [false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false,true,true,false] [] [true,true,false] [true,true,true] false (.lit [true]) (.lit []) 3,
   .steps 81],6,0,162⟩
theorem check_cert : Tails.check table cert = true := by decide +kernel
def family (n : Nat) : Z0 := cert.source.eval n 0 [] []
theorem seed : run0 table 3382 ⟨0,[],[]⟩ = some (family 0) := by decide +kernel
theorem grow (n : Nat) : run0 table (6*n+162) (family n) = some (family (n+1)) := by
  simpa [family,cert,Tails.PZ.eval,Tails.Word.eval,rep,List.append_assoc] using
    Tails.check_sound table cert check_cert n 0 [] []
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  never_of_growth table family 3382 (fun n => 6*n+162) seed (fun n => by omega) grow m hm
theorem cover (B : Nat) : Cover (WeightedBound B) table :=
  .leaf _ fun m hm => weighted_never B m (never m hm)
#print axioms cover
end BB6Coverage.Agent31Pump.Raw11Q0Sweep150
