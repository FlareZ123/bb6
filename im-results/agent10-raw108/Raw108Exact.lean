import Raw108Closed
import Raw108LBExact
import Raw108LongAttained
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10Raw108Exact
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent10Raw108Root
/-- All twenty residual children and the four already-certified root cycles.
The theorem is unconditional once all original-source dependencies compile. -/
theorem exact_upper (m : Machine) (hm : compatible parent m) : WeightedBound 4136175 m := by
  rcases parent_dichotomy m hm with hb | ⟨mv,hr,hc⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
  · simp only [remaining,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108B0LA.all_completions m hc k d hk hd) (by decide)
    · exact fun k d hk hd => Nat.le_trans (BB6.Agent10Raw108LBExact.exact_upper m hc k d hk hd) (by decide)
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
/-- The weighted maximum of this parent cylinder, including every compatible completion. -/
theorem exact_bound (B : Nat) :
    (∀ m, compatible parent m → WeightedBound B m) ↔ 4136175 ≤ B := by
  constructor
  · exact BB6.Agent10Raw108Long.raw108_lower B
  · intro h m hm k d hk hd
    exact Nat.le_trans (exact_upper m hm k d hk hd) h

#print axioms exact_upper
#print axioms exact_bound
end BB6.Agent10Raw108Exact
