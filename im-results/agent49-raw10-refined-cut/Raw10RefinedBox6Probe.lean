import Raw10RefinedBox7
import Box6SourceConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent49Raw10RefinedBox6Probe

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109 BB6.Agent49Box BB6.Agent50RootFrontier
open BB6.Agent49Raw10RefinedCut

def add6 (cs : List RBox) : List RBox := cs ++ [raw10Remainder[6]!]

#check BB6.Agent49Box6.raw10_box6_closed
#check BB6.Agent49Box6.box6_weighted
#check BB6.Agent49Box6.residual_without_box6

#eval (openBoxes (add6
  (BB6.Agent49Raw10RefinedBox7.add7
    (BB6.Agent49Raw10RefinedBox5.add5 accepted)))).length

#eval (openBoxes (add6
  (BB6.Agent49Raw10RefinedBox7.add7
    (BB6.Agent49Raw10RefinedBox5.add5 candidate)))).length

end BB6.Agent49Raw10RefinedBox6Probe
