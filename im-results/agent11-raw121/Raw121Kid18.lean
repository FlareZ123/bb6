import Raw121Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid18 : Audit := .cycle 0 9 true (0)

theorem check18 : zipCheck 4063 (child121 ⟨true,true,0⟩) kid18 = true := by decide

end BB6.Agent11Raw121
