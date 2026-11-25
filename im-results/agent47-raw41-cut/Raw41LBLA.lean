import CanonicalFrontier
import ZipThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47CanonicalFrontier

/-- Raw41: D1 = 1RA, the authentic divergence after three path moves. -/
abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨true,true,0⟩)
abbrev child (mv : Move) : PartialMachine := refine parent (0,true) (some mv)
abbrev lbla : PartialMachine := refine (child ⟨false,false,1⟩) (1,true) (some ⟨false,false,0⟩)

/-- Three-state finite automata reduction, uniformly treating every unknown
    table entry as a potential halt. -/
def lblaCert : FAR.Data 3 :=
  ⟨0,[0,1,2,1,0,1],
  [128,256,8,295360,262144,262144,128,256,32768,32896,262144,262144,128,256,8,320,262144,262144,262144],
  [32768,256,262144,64,262144,262144,32896,320,262144,64,262144,262144,32768,256,262144,64,262144,262144,262144],478268⟩

theorem lbla_checked : lblaCert.fastValid lbla = true := by decide +kernel

theorem lbla_never (m : Machine) (hm : compatible lbla m) : NeverHalts m :=
  farSound lbla false lblaCert lbla_checked m hm

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)

theorem parent_query : zipQueryOK 7014 parent 6 (0,true) = true := by decide

theorem child_query : zipQueryOK 7014 (child ⟨false,false,1⟩) 7 (1,true) = true := by decide

#print axioms lbla_checked
#print axioms lbla_never
#print axioms parent_query
#print axioms child_query
end BB6.Agent47Raw41
