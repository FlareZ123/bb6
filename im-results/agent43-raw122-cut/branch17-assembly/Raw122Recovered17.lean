import BB6Coverage
import Raw122Base
import Raw122Roster17
import Raw122Roster17Witnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered17
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem cover17 (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨true,false,5⟩) m) :
    WeightedBound 6766859 m := by
  exact BB6.Agent43Raw122Roster.cover17 6766859 (by decide)
    BB6.Agent43Raw122Roster.witnesses17 m hm
theorem residual_count : BB6.Agent43Raw122Roster.tables17.length = 24 := by decide
#print axioms cover17
#print axioms residual_count
end BB6.Agent43Raw122Recovered17
