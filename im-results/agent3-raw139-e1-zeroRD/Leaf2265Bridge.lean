import Leaf2265BridgeCore
import Leaf2265Trace

namespace BB6.Agent3Leaf2265Bridge
open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent3Leaf2265 (terminalCfg terminalRun terminalRead)

/-- Exact first query from the genuine blank root; source-counted trace. -/
def n : Nat := 808309055302710301732399105636921133919495108874980019743107699471600464749233442847378894817095810992429166948707568686931771651390236209884096433253525595914426390935828906878170789519869183115472163083845213146412559801558627

theorem reached (m : Machine) (hm : compatible ctr m) :
    ∃ c, BB6Coverage.run m n BB6Coverage.blank = some c ∧
      readSlot c = (4,false) := by
  exact reached_of_source m hm n terminalCfg terminalRun terminalRead

theorem weighted : Cover (WeightedBound (n+6)) ctr :=
  weighted_of_source n terminalCfg terminalRun terminalRead


/-- The literal closingMachine halts after exactly 228-digit n successful
    moves and its final halt query, realizing the score n+1. In particular
    this is a genuine source-derived six-state attainable lower bound, not
    a simulation cut-off or a proposed arithmetic runtime. -/
theorem exact_attainable : Attainable (n+1) :=
  attainable_of_source n terminalCfg terminalRun terminalRead

#print axioms exact_attainable

#print axioms reached
#print axioms weighted
end BB6.Agent3Leaf2265Bridge
