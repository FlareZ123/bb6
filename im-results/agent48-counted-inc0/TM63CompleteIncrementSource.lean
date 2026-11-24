import TM63SourceIncrementDispatcher
import M0EvenEightValuationCountedSource
import M2EvenResidueZeroCounted
import TM63DirectRootComposition

namespace BB6Coverage.Agent48DirectRoot
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48M0EvenEightValuationCountedSource
open BB6Coverage.Agent24M2EvenCounted

/-- Every positive counter in every width at least three follows the counted source law. -/
theorem increment_source : IncrementSource := by
  intro L n m a b h hL hn hb ha
  exact tm63_source_increment_dispatch_ge3 L hL
    (fun q aa bb hh hq h4 hb ha =>
      m0EvenEight_valuation_counted_increment_source L q aa bb hh h4 hq hb ha)
    (fun q aa bb hh hq h4 hb ha =>
      m2Even_residue0_counted_increment_source L q aa bb hh h4 hq hb ha)
    n m a b h hn hb ha

#print axioms increment_source
end BB6Coverage.Agent48DirectRoot
