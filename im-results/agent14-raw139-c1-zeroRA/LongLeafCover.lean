import LongLeafAdapter
import Result78
namespace BB6.Agent14C1ZeroRALong
open BB6Coverage BB6.Agent13BlankDelay BB6.CoverageAdapter

theorem table_eq : toAgent13Machine m0 = BB6.Agent41SegmentTrace.table := by
  funext q b
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem weighted : Cover (WeightedBound 14876970) p := by
  apply long_cover
  rw [table_eq]
  exact BB6.Agent41SegmentTrace.halt78

#print axioms weighted
end BB6.Agent14C1ZeroRALong
