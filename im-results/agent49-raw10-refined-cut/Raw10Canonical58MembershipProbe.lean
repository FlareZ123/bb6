import Canonical58Raw113Graft
import Raw10RefinedCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10Canonical58MembershipProbe

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement
open BB6.Agent31StableParentBatch BB6.Agent49BoxBridge

abbrev p10 : PartialMachine := BB6.Agent49BoxBridge.firstOneB0_1LC

#check p10
#check BB6.Agent3Canonical64Raw120.roster64
#check BB6.Agent32CanonicalSelectedIntegrated.rosterSelected
#check BB6.Agent31Canonical58Raw113Graft.roster58

#eval (BB6.Agent3Canonical64Raw120.roster64.filter
  (fun e => sameTable e.2 p10)).length

#eval (BB6.Agent32CanonicalSelectedIntegrated.rosterSelected.filter
  (fun e => sameTable e.2 p10)).length

#eval (BB6.Agent31Canonical58Raw113Graft.roster58.filter
  (fun e => sameTable e.2 p10)).length

#eval (BB6.Agent31Canonical58Raw113Graft.roster58.filter
  (fun e => sameTable e.2 p10)).map Prod.fst

#eval p10 initialSlot

end BB6.Agent49Raw10Canonical58MembershipProbe
