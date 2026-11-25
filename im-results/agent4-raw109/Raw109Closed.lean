import Raw109Cut
import Raw109B0LAData
import Raw109B0LCData
import Raw109B0LFData
import Raw109B0RCData
import Raw109B0RFData
import Raw109B1LAData
import Raw109B1LBData
import Raw109B1LCData
import Raw109B1LFData
import Raw109B1REData
import Raw109B1RFData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw109Closed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent4Raw109Cut

/-- No exception hypotheses: every compatible completion of raw109 has
weighted bound 1703. The source checker validates each child independently. -/
theorem all_closed (m : Machine) (hm : compatible parent m) : WeightedBound 1703 m := by
  rcases parent_dichotomy m hm with hb | ⟨mv,hr,hc⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
  · simp only [remaining,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B0LA.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B0LC.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B0LF.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B0RC.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B0RF.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B1LA.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B1LB.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B1LC.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B1LF.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B1RE.all_closed m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent4Raw109B1RF.all_closed m hc k d hk hd) (by decide)

#print axioms all_closed
end BB6.Agent4Raw109Closed
