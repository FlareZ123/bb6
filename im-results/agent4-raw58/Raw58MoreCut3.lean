import Raw58MoreCut2
import Raw58LEData
import Raw58LFData
import Raw58RFData
import Raw58LE1Data
import Raw58LF1Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent4Raw58MoreCut3

theorem all_completions :
    ∀ m, compatible BB6.Agent4Raw58MoreCut2.parent m → WeightedBound 3055750 m := by
  intro m hm
  rcases BB6.Agent4Raw58MoreCut2.parent_dichotomy m hm with hb | ⟨mv, hr, hc⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have hrem :
        BB6.Agent4Raw58MoreCut2.remaining =
          [⟨false,false,4⟩, ⟨false,false,5⟩, ⟨false,true,5⟩,
           ⟨true,false,4⟩, ⟨true,false,5⟩] := by decide
    rw [hrem] at hr
    simp only [List.mem_cons] at hr
    rcases hr with h0 | h1 | h2 | h3 | h4 | hnil
    · subst mv
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent4Raw58LE.all_completions m hc k d hk hd) (by decide)
    · subst mv
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent4Raw58LF.all_completions m hc k d hk hd) (by decide)
    · subst mv
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent4Raw58RF.all_completions m hc k d hk hd) (by decide)
    · subst mv
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent4Raw58LE1.all_completions m hc k d hk hd) (by decide)
    · subst mv
      intro k d hk hd
      exact Nat.le_trans (BB6.Agent4Raw58LF1.all_completions m hc k d hk hd) (by decide)
    · cases hnil

#print axioms all_completions

end BB6.Agent4Raw58MoreCut3
