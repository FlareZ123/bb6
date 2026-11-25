import Raw39Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid00 : Audit := .cycle 1 8 true (1)

theorem check00 : zipCheck 175 (child39 ⟨false,false,0⟩) kid00 = true := by decide

end BB6.Agent11Raw39
