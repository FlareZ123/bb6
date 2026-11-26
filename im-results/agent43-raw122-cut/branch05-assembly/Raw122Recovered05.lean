import BB6Coverage
import Raw122Base
import Raw122Roster05Witnesses
import LateCheck0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered05
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem cover05 (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨false,false,5⟩) m) :
    WeightedBound 6766859 m := by
  have hLate : BB6.Agent43Raw122ResidualCompose.Covered 6766859
      BB6.Agent43Raw122Roster.p05_007 :=
    BB6Coverage.Agent29PackedLate.M0.bound
  exact BB6.Agent43Raw122Roster.cover05 6766859 (by decide)
    (BB6.Agent43Raw122Roster.witnesses05 hLate) m hm

theorem residual_count : BB6.Agent43Raw122Roster.tables05.length = 20 := by decide
#print axioms cover05
#print axioms residual_count
end BB6.Agent43Raw122Recovered05
