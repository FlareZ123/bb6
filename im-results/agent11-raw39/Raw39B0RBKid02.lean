import Raw39B0RBBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B0RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid02 : Audit := .cycle 16 1 false (2)

theorem check02 : zipCheck 1271 (child ⟨false,false,2⟩) kid02 = true := by decide

end BB6.Agent11Raw39B0RB
