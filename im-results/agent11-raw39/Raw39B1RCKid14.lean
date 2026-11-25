import Raw39B1RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39B1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid14 : Audit := .cycle 2 10 true (1)

theorem check14 : zipCheck 1882 (child ⟨true,false,2⟩) kid14 = true := by decide

end BB6.Agent11Raw39B1RC
