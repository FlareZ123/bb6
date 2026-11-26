import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent12Raw124ZeroLFTrivial
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev p124 : PartialMachine := refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev pBranch : PartialMachine := refine p124 (5,true) (some ⟨false,false,5⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem pBranch_nohalt : weightedTNFNoAssignedHalt pBranch := weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt
abbrev p0LA : PartialMachine := refine pBranch (5,false) (some ⟨false,false,0⟩)
theorem never0LA (m : Machine) (hm : compatible p0LA m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0LA 0 10 false (3) (by decide) (by decide) m hm
#print axioms never0LA
abbrev p0LB : PartialMachine := refine pBranch (5,false) (some ⟨false,false,1⟩)
theorem never0LB (m : Machine) (hm : compatible p0LB m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0LB 8 8 false (0) (by decide) (by decide) m hm
#print axioms never0LB
abbrev p0LC : PartialMachine := refine pBranch (5,false) (some ⟨false,false,2⟩)
theorem never0LC (m : Machine) (hm : compatible p0LC m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0LC 11 1 false (-1) (by decide) (by decide) m hm
#print axioms never0LC
abbrev p0LD : PartialMachine := refine pBranch (5,false) (some ⟨false,false,3⟩)
theorem never0LD (m : Machine) (hm : compatible p0LD m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0LD 10 1 false (-2) (by decide) (by decide) m hm
#print axioms never0LD
abbrev p0LF : PartialMachine := refine pBranch (5,false) (some ⟨false,false,5⟩)
theorem never0LF (m : Machine) (hm : compatible p0LF m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0LF 9 1 false (-1) (by decide) (by decide) m hm
#print axioms never0LF
abbrev p0RC : PartialMachine := refine pBranch (5,false) (some ⟨false,true,2⟩)
theorem never0RC (m : Machine) (hm : compatible p0RC m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0RC 11 1 false (1) (by decide) (by decide) m hm
#print axioms never0RC
abbrev p0RD : PartialMachine := refine pBranch (5,false) (some ⟨false,true,3⟩)
theorem never0RD (m : Machine) (hm : compatible p0RD m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0RD 10 1 false (0) (by decide) (by decide) m hm
#print axioms never0RD
abbrev p0RF : PartialMachine := refine pBranch (5,false) (some ⟨false,true,5⟩)
theorem never0RF (m : Machine) (hm : compatible p0RF m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p0RF 16 1 true (2) (by decide) (by decide) m hm
#print axioms never0RF
abbrev p1LD : PartialMachine := refine pBranch (5,false) (some ⟨true,false,3⟩)
theorem never1LD (m : Machine) (hm : compatible p1LD m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p1LD 10 1 false (-2) (by decide) (by decide) m hm
#print axioms never1LD
abbrev p1LF : PartialMachine := refine pBranch (5,false) (some ⟨true,false,5⟩)
theorem never1LF (m : Machine) (hm : compatible p1LF m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p1LF 9 1 false (-1) (by decide) (by decide) m hm
#print axioms never1LF
abbrev p1RD : PartialMachine := refine pBranch (5,false) (some ⟨true,true,3⟩)
theorem never1RD (m : Machine) (hm : compatible p1RD m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p1RD 8 5 false (0) (by decide) (by decide) m hm
#print axioms never1RD
abbrev p1RF : PartialMachine := refine pBranch (5,false) (some ⟨true,true,5⟩)
theorem never1RF (m : Machine) (hm : compatible p1RF m) : NeverHalts m :=
  BB6Coverage.Agent10ZipAudit.zipCycle_sound p1RF 27 1 true (-3) (by decide) (by decide) m hm
#print axioms never1RF
end BB6.Agent12Raw124ZeroLFTrivial
