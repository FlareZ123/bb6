import BB6Coverage
import Raw122Base
import Raw122Roster16
import Raw122Roster16Witnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered16
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem cover16 (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨true,false,4⟩) m) :
    WeightedBound 6766859 m := by
  exact BB6.Agent43Raw122Roster.cover16 6766859 (by decide)
    BB6.Agent43Raw122Roster.witnesses16 m hm
theorem residual_count : BB6.Agent43Raw122Roster.tables16.length = 13 := by decide
#print axioms cover16
#print axioms residual_count
end BB6.Agent43Raw122Recovered16
