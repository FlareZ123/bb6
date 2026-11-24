import F418Rules
namespace BB6.Agent32F418
open BB6.Agent32FiniteSource
def seedRight : List Bool := [true,false,true,true,true,false,true,false,true,false,true,true,true,false,true,true,true,false,true,false,true,false,true,true,true,false,true,true,true,true,true,false,true,false,true,true]
set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem seed : Run 670 finiteBlank (cfg 3 [] false seedRight) := by unfold Run; decide
#print axioms seed
end BB6.Agent32F418
