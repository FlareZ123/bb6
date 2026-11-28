import Raw42GlobalBridge
import Raw420LAClosedCover
import Raw420RAClosedCover
import Raw421LAClosedCover
import Raw421RAClosedCover
import Raw420RBClosedCover
import Raw421LBClosedCover
import Raw421RBClosedCover
import Raw421LCClosedCover
import Raw420LEClosedCover
import Raw420REClosedCover
import Raw421LEClosedCover
import Raw421REClosedCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw42AcceptedParent
open BB6Coverage

theorem cover_global :
    Cover (BB6.Agent13BlankDelay.WeightedBound 6766859)
      BB6.Agent17Raw42GlobalBridge.literal :=
  BB6.Agent17Raw42GlobalBridge.global_cover_from_named
    BB6.Agent32Raw420LA.Closed.cover
    BB6.Agent32Raw420RA.Closed.cover
    BB6.Agent32Raw421LA.Closed.cover
    BB6.Agent32Raw421RA.Closed.cover
    BB6.Agent32Raw420RB.Closed.cover
    BB6.Agent32Raw421LB.Closed.cover
    BB6.Agent32Raw421RB.Closed.cover
    BB6.Agent32Raw421LC.Closed.cover
    BB6.Agent32Raw420LE.Closed.cover
    BB6.Agent32Raw420RE.Closed.cover
    BB6.Agent32Raw421LE.Closed.cover
    BB6.Agent32Raw421RE.Closed.cover

#print axioms cover_global
end BB6.Agent17Raw42AcceptedParent
