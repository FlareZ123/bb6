import Raw39B1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid08 : Audit := .far false 1 ⟨0,[0, 0],[2, 4, 8, 4, 64, 64, 64],[4, 64, 4, 1, 64, 64, 64],112⟩

theorem check08 : zipCheck 1882 (child ⟨false,true,2⟩) kid08 = true := by decide

end BB6.Agent11Raw39B1RC
