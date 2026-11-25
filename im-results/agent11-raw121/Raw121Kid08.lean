import Raw121Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid08 : Audit := .cycle 6 9 true (2)

theorem check08 : zipCheck 4063 (child121 ⟨false,true,2⟩) kid08 = true := by decide

end BB6.Agent11Raw121
