import Raw42Cut
import Raw42NestedGrowth

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
namespace BB6.Agent32Raw42NestedCuts

abbrev subOneLBZeroLD : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,1⟩) (2,true) (some ⟨false,false,3⟩)

theorem eqOneLBZeroLD : subOneLBZeroLD = BB6.Agent32Raw42Nested.OneLBZeroLD.p := by
  apply tableOK_sound
  decide

theorem coverOneLBZeroLD (B : Nat) : Cover (WeightedBound B) subOneLBZeroLD := by
  refine .leaf subOneLBZeroLD ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Nested.OneLBZeroLD.never m (eqOneLBZeroLD ▸ hm))
#print axioms coverOneLBZeroLD

abbrev subOneLBZeroRD : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,1⟩) (2,true) (some ⟨false,true,3⟩)

theorem eqOneLBZeroRD : subOneLBZeroRD = BB6.Agent32Raw42Nested.OneLBZeroRD.p := by
  apply tableOK_sound
  decide

theorem coverOneLBZeroRD (B : Nat) : Cover (WeightedBound B) subOneLBZeroRD := by
  refine .leaf subOneLBZeroRD ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Nested.OneLBZeroRD.never m (eqOneLBZeroRD ▸ hm))
#print axioms coverOneLBZeroRD

abbrev subOneLCOneLC : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,2⟩) (2,true) (some ⟨true,false,2⟩)

theorem eqOneLCOneLC : subOneLCOneLC = BB6.Agent32Raw42Nested.OneLCOneLC.p := by
  apply tableOK_sound
  decide

theorem coverOneLCOneLC (B : Nat) : Cover (WeightedBound B) subOneLCOneLC := by
  refine .leaf subOneLCOneLC ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Nested.OneLCOneLC.never m (eqOneLCOneLC ▸ hm))
#print axioms coverOneLCOneLC

end BB6.Agent32Raw42NestedCuts
