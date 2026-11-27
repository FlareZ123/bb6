import A6Entry77
import A6Entry78
import A6Cycle77
import A6Cycle78
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6D1TwoCycles
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent6OneSide BB6Coverage.Agent6PackedSweep
open BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6Coverage.Agent10ZipAudit
def W : List Bool := [false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,true,true,false,false,false,false,true,true,false,true,true,true,true,false,false,true,true,false,true,true,true,true,false,false,true,true,false,true,true,true,true,true,true,false,true,true,true,true,false,true,true,false,false,false]
def V : List Bool := [false,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,false,false,false,false,true,true,false,true,true,true,true,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,true,true]
def T : List Bool := [false,false,false,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,true,true,false,true,true,true,true,false,true,true,true,true,false,false,true,true,false,false,false,false,true,true,false,true,true,true,true,false,false,false,true,true,false,false,false,false,false,false,true,true,false,false,false,false,false,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,false,false,true,true,false,false,false,true,true,false,true,true,true,true,true,true,false,true,true,true,true,true,true,false,true,true,false,true,true,true,true,false,false,false,false,false,false,false,false,true,true,false,true,true,false,true,true,true,true,true,true,false,false,false,true,true,false,true,true,true,true,true,true,true,true,false,false,true,true,false,true,true,true,true,true,true,false,true,true,true,true,false,false,false,true,true,false,true,true,true,true,false,false,true,true,false,true,true,true,true,true,true,false,true,true,true,true]

theorem first77 : run0 A6Entry77.p 32835 ⟨0,[],[]⟩ = some ⟨3,W++T,[]⟩ :=
  reach_exact A6Entry77.p 32835 ⟨3,W++T,[]⟩ A6Entry77.reached

theorem cycle77 (L : List Bool) : run0 A6Entry77.p 16333 ⟨3,W++L,[]⟩ = some ⟨3,W++V++L,[]⟩ := by
  have H := A6Cycle77.cycle L
  change run0 A6Entry77.p 16333 ⟨3,W++L,[]⟩ = some ⟨3,(W++V)++L,[]⟩ at H
  exact H

theorem never77 (m : Machine) (hm : compatible A6Entry77.p m) : NeverHalts m :=
  right_growth A6Entry77.p 3 W V T 32835 16333 first77 (by decide) cycle77 m hm

theorem cover77 (B : Nat) : Cover (WeightedBound B) A6Entry77.p := by
  exact .leaf _ (fun m hm => weighted_never B m (never77 m hm))
#print axioms cover77

theorem first78 : run0 A6Entry78.p 30903 ⟨0,[],[]⟩ = some ⟨3,W++T,[]⟩ :=
  reach_exact A6Entry78.p 30903 ⟨3,W++T,[]⟩ A6Entry78.reached

theorem cycle78 (L : List Bool) : run0 A6Entry78.p 15373 ⟨3,W++L,[]⟩ = some ⟨3,W++V++L,[]⟩ := by
  have H := A6Cycle78.cycle L
  change run0 A6Entry78.p 15373 ⟨3,W++L,[]⟩ = some ⟨3,(W++V)++L,[]⟩ at H
  exact H

theorem never78 (m : Machine) (hm : compatible A6Entry78.p m) : NeverHalts m :=
  right_growth A6Entry78.p 3 W V T 30903 15373 first78 (by decide) cycle78 m hm

theorem cover78 (B : Nat) : Cover (WeightedBound B) A6Entry78.p := by
  exact .leaf _ (fun m hm => weighted_never B m (never78 m hm))
#print axioms cover78
end BB6.Agent6D1TwoCycles
