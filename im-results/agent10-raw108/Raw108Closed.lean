import Raw108RootCut
import Raw108B0LAData
import Raw108B0LBData
import Raw108B0LCData
import Raw108B0LDData
import Raw108B0LEData
import Raw108B0LFData
import Raw108B0RAData
import Raw108B0RCData
import Raw108B0RDData
import Raw108B0REData
import Raw108B0RFData
import Raw108B1LAData
import Raw108B1LBData
import Raw108B1LCData
import Raw108B1LEData
import Raw108B1LFData
import Raw108B1RAData
import Raw108B1RCData
import Raw108B1RDData
import Raw108B1RFData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108Closed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10Raw108Root
/-- All twenty residual children and the four already-certified root cycles.
The theorem is unconditional once all original-source dependencies compile. -/
theorem all_closed (m : Machine) (hm : compatible parent m) : WeightedBound 4136180 m := by
  rcases parent_dichotomy m hm with hb | ⟨mv,hr,hc⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
  · simp only [remaining,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LA.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LB.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LC.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LD.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LE.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LF.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0RA.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0RC.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0RD.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0RE.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0RF.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1LA.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1LB.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1LC.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1LE.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1LF.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1RA.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1RC.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1RD.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B1RF.all_completions m hc k d hk hd) (by decide)
#print axioms all_closed
end BB6.Agent10Raw108Closed
