import Canonical63Raw112Integrated
import Raw122Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent43Raw122Canonical63

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier
open BB6.Agent3Canonical64Raw120
open BB6.Agent31Canonical63Raw112
open BB6.Agent43Raw122

/-- Raw122 remains a unique representative after the already accepted
    Raw112 parent has been removed from the 64-entry roster. -/
abbrev p122 : PartialMachine := BB6.Agent43Raw122.parent

theorem p122_count63 :
    (roster63.filter (fun e => sameTable e.2 p122)).length = 1 := by
  decide

#eval roster63.findIdx (fun e => sameTable e.2 p122)

#print axioms p122_count63

end BB6.Agent43Raw122Canonical63
