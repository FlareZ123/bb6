import BB6Coverage
import Raw122Base
import Raw122Roster00
import Raw122Roster00Witnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered00
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem cover00 (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨false,false,0⟩) m) :
    WeightedBound 6766859 m := by
  exact BB6.Agent43Raw122Roster.cover00 6766859 (by decide)
    BB6.Agent43Raw122Roster.witnesses00 m hm
theorem residual_count : BB6.Agent43Raw122Roster.tables00.length = 28 := by decide
#print axioms cover00
#print axioms residual_count
end BB6.Agent43Raw122Recovered00
