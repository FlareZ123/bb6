import Agent46CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent46CanonicalCut

/-- Canonical residual raw13: A0=1RB, B0=1RC, C0=1LA. -/
def afterB : PartialMachine := refine root (1,false) (some ⟨true,true,2⟩)
def raw13 : PartialMachine := refine afterB (2,false) (some ⟨true,false,0⟩)
theorem raw13_root : raw13 initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem raw13_nohalt : weightedTNFNoAssignedHalt raw13 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _ firstOneCylinder_no_assigned_halt)
theorem raw13_support : TNFSupport raw13 3 := by
  have h0 : TNFSupport root 2 := by
    simpa [root] using firstOneCylinder_tnf_support
  have h1 : TNFSupport afterB 3 :=
    refine_support root (1,false) ⟨true,true,2⟩ 2 3 h0 (by decide) (by decide) (by decide)
  exact refine_support afterB (2,false) ⟨true,false,0⟩ 3 3 h1 (by decide) (by decide) (by decide)

def child (mv : Move) : PartialMachine := refine raw13 (0,true) (some mv)

#print axioms raw13_support
end BB6.Agent46Raw13
