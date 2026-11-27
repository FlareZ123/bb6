import Raw42Cut
import Raw42WideGrowth

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
namespace BB6.Agent32Raw42WideCuts

abbrev subZeroLAOneRC : PartialMachine := refine (BB6.Agent32Raw42.child ⟨false,false,0⟩) (0,true) (some ⟨true,true,2⟩)

theorem eqZeroLAOneRC : subZeroLAOneRC = BB6.Agent32Raw42Wide.ZeroLAOneRC.p := by
  apply tableOK_sound
  decide

theorem coverZeroLAOneRC (B : Nat) : Cover (WeightedBound B) subZeroLAOneRC := by
  refine .leaf subZeroLAOneRC ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.ZeroLAOneRC.never m (eqZeroLAOneRC ▸ hm))
#print axioms coverZeroLAOneRC

abbrev subOneLAZeroRD : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,0⟩) (0,true) (some ⟨false,true,3⟩)

theorem eqOneLAZeroRD : subOneLAZeroRD = BB6.Agent32Raw42Wide.OneLAZeroRD.p := by
  apply tableOK_sound
  decide

theorem coverOneLAZeroRD (B : Nat) : Cover (WeightedBound B) subOneLAZeroRD := by
  refine .leaf subOneLAZeroRD ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneLAZeroRD.never m (eqOneLAZeroRD ▸ hm))
#print axioms coverOneLAZeroRD

abbrev subOneLCZeroRB : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,2⟩) (2,true) (some ⟨false,true,1⟩)

theorem eqOneLCZeroRB : subOneLCZeroRB = BB6.Agent32Raw42Wide.OneLCZeroRB.p := by
  apply tableOK_sound
  decide

theorem coverOneLCZeroRB (B : Nat) : Cover (WeightedBound B) subOneLCZeroRB := by
  refine .leaf subOneLCZeroRB ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneLCZeroRB.never m (eqOneLCZeroRB ▸ hm))
#print axioms coverOneLCZeroRB

abbrev subOneLCZeroRD : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,2⟩) (2,true) (some ⟨false,true,3⟩)

theorem eqOneLCZeroRD : subOneLCZeroRD = BB6.Agent32Raw42Wide.OneLCZeroRD.p := by
  apply tableOK_sound
  decide

theorem coverOneLCZeroRD (B : Nat) : Cover (WeightedBound B) subOneLCZeroRD := by
  refine .leaf subOneLCZeroRD ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneLCZeroRD.never m (eqOneLCZeroRD ▸ hm))
#print axioms coverOneLCZeroRD

abbrev subOneRBOneLC : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,true,1⟩) (2,true) (some ⟨true,false,2⟩)

theorem eqOneRBOneLC : subOneRBOneLC = BB6.Agent32Raw42Wide.OneRBOneLC.p := by
  apply tableOK_sound
  decide

theorem coverOneRBOneLC (B : Nat) : Cover (WeightedBound B) subOneRBOneLC := by
  refine .leaf subOneRBOneLC ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneRBOneLC.never m (eqOneRBOneLC ▸ hm))
#print axioms coverOneRBOneLC

abbrev subOneLBOneRC : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,false,1⟩) (2,true) (some ⟨true,true,2⟩)

theorem eqOneLBOneRC : subOneLBOneRC = BB6.Agent32Raw42Wide.OneLBOneRC.p := by
  apply tableOK_sound
  decide

theorem coverOneLBOneRC (B : Nat) : Cover (WeightedBound B) subOneLBOneRC := by
  refine .leaf subOneLBOneRC ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneLBOneRC.never m (eqOneLBOneRC ▸ hm))
#print axioms coverOneLBOneRC

abbrev subOneREOneLD : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,true,4⟩) (4,false) (some ⟨true,false,3⟩)

theorem eqOneREOneLD : subOneREOneLD = BB6.Agent32Raw42Wide.OneREOneLD.p := by
  apply tableOK_sound
  decide

theorem coverOneREOneLD (B : Nat) : Cover (WeightedBound B) subOneREOneLD := by
  refine .leaf subOneREOneLD ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneREOneLD.never m (eqOneREOneLD ▸ hm))
#print axioms coverOneREOneLD

abbrev subOneRBZeroRC : PartialMachine := refine (BB6.Agent32Raw42.child ⟨true,true,1⟩) (2,true) (some ⟨false,true,2⟩)

theorem eqOneRBZeroRC : subOneRBZeroRC = BB6.Agent32Raw42Wide.OneRBZeroRC.p := by
  apply tableOK_sound
  decide

theorem coverOneRBZeroRC (B : Nat) : Cover (WeightedBound B) subOneRBZeroRC := by
  refine .leaf subOneRBZeroRC ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42Wide.OneRBZeroRC.never m (eqOneRBZeroRC ▸ hm))
#print axioms coverOneRBZeroRC

end BB6.Agent32Raw42WideCuts
