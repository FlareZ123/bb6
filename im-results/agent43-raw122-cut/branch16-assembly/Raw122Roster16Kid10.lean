import Raw122Kid16_10
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
theorem kid16_10_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨true,false,4⟩) (5,false) (some ⟨false,true,4⟩)) kid16_10).map Prod.snd = [] := by
  rfl
end BB6.Agent43Raw122Roster
