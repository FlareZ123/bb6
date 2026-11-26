import Raw122Kid05_21
import Raw122ResidualCompose
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Roster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6.Agent43Raw122 BB6.Agent43Raw122ResidualCompose
theorem kid05_21_roster : (partialResiduals (refine (BB6.Agent43Raw122.child ⟨false,false,5⟩) (5,false) (some ⟨true,true,3⟩)) kid05_21).map Prod.snd = [] := by
  rfl
end BB6.Agent43Raw122Roster
