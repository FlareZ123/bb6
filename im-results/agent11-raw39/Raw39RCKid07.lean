import Raw39RCBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11Raw39RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
def kid07 : Audit := .cycle 1 7 true (1)

theorem check07 : zipCheck 2354 (childRC ⟨false,true,1⟩) kid07 = true := by decide

end BB6.Agent11Raw39RC
