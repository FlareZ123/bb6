import Raw58LEData
import Raw58LFData
import Raw58RFData
import Raw58LE1Data
import Raw58LF1Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw58SharpComposition
open BB6Coverage BB6.Agent13BlankDelay

abbrev p58 : PartialMachine := BB6.Agent4Raw58LF1.p58
abbrev child (mv : Move) : PartialMachine := refine p58 (0,true) (some mv)
def remaining : List Move :=
  [⟨false,false,4⟩, ⟨false,false,5⟩, ⟨false,true,5⟩,
   ⟨true,false,4⟩, ⟨true,false,5⟩]

theorem raw58_lower (B : Nat) (h : ∀ m, compatible p58 m → WeightedBound B m) : 3055746 ≤ B := by
  apply BB6.Agent4Raw58LF1.lower B
  intro m hm
  exact h m (refine_preserves_compat p58 m (0,true) (some ⟨true,false,5⟩) (by decide) hm)

/-- Exact closure given the independently audited first-hole partition. -/
theorem raw58_bound
    (hcut : ∀ m, compatible p58 m → WeightedBound 374 m ∨ ∃ mv ∈ remaining, compatible (child mv) m) :
    ∀ m, compatible p58 m → WeightedBound 3055746 m := by
  intro m hm
  rcases hcut m hm with hb | ⟨mv, hr, hc⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · simp only [remaining,List.mem_cons] at hr
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
      exact BB6.Agent4Raw58LF1.bound m hc
    · cases hnil

theorem raw58_exact
    (hcut : ∀ m, compatible p58 m → WeightedBound 374 m ∨ ∃ mv ∈ remaining, compatible (child mv) m)
    (B : Nat) : (∀ m, compatible p58 m → WeightedBound B m) ↔ 3055746 ≤ B := by
  constructor
  · exact raw58_lower B
  · intro h m hm k d hk hd
    exact Nat.le_trans (raw58_bound hcut m hm k d hk hd) h

#print axioms raw58_lower
#print axioms raw58_bound
#print axioms raw58_exact
end BB6.Agent4Raw58SharpComposition
