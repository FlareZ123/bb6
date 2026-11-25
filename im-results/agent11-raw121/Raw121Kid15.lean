import Raw121Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid15 : Audit := .cycle 7 3 true (3)

theorem check15 : zipCheck 4063 (child121 ⟨true,false,3⟩) kid15 = true := by decide

end BB6.Agent11Raw121
