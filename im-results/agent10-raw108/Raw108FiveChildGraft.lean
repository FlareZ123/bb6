import Raw108RootCut
import Raw108B0RDData
import Raw108B0LCData
import Raw108B1RCData
import Raw108B1RDData
import Raw108B0REData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10Raw108Graft

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent10Raw108Root

/-- Five raw108 children whose complete weighted certificates have passed
    original-source Lean audits: 0RD, 0LC, 1RC, 1RD, and 0RE. -/
def certifiedChildren : List Move :=
  [⟨false,true,3⟩, ⟨false,false,2⟩, ⟨true,true,2⟩,
   ⟨true,false,3⟩, ⟨false,true,4⟩]

/-- The exact remaining child partition after consuming those five proofs. -/
def residual : List Move :=
  remaining.filter fun mv => !(decide (mv ∈ certifiedChildren))

theorem certifiedChildren_count : certifiedChildren.length = 5 := by
  decide

theorem residual_count : residual.length = 15 := by
  decide

private theorem liftBound {b : Nat} {m : Machine}
    (hB : b ≤ 7014) (h : WeightedBound b m) :
    WeightedBound 7014 m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hB

theorem child_0RD_bound (m : Machine)
    (hm : compatible (child ⟨false,true,3⟩) m) :
    WeightedBound 7014 m := by
  have hm' : compatible BB6.Agent10Raw108B0RD.parent m := hm
  exact liftBound (by decide)
    (BB6.Agent10Raw108B0RD.all_completions m hm')

theorem child_0LC_bound (m : Machine)
    (hm : compatible (child ⟨false,false,2⟩) m) :
    WeightedBound 7014 m := by
  have hm' : compatible BB6.Agent10Raw108B0LC.parent m := hm
  exact liftBound (by decide)
    (BB6.Agent10Raw108B0LC.all_completions m hm')

theorem child_1RC_bound (m : Machine)
    (hm : compatible (child ⟨true,true,2⟩) m) :
    WeightedBound 7014 m := by
  have hm' : compatible BB6.Agent10Raw108B1RC.parent m := hm
  exact liftBound (by decide)
    (BB6.Agent10Raw108B1RC.all_completions m hm')

theorem child_1RD_bound (m : Machine)
    (hm : compatible (child ⟨true,true,3⟩) m) :
    WeightedBound 7014 m := by
  have hm' : compatible BB6.Agent10Raw108B1RD.parent m := hm
  exact liftBound (by decide)
    (BB6.Agent10Raw108B1RD.all_completions m hm')

theorem child_0RE_bound (m : Machine)
    (hm : compatible (child ⟨false,true,4⟩) m) :
    WeightedBound 7014 m := by
  have hm' : compatible BB6.Agent10Raw108B0RE.parent m := hm
  exact liftBound (by decide)
    (BB6.Agent10Raw108B0RE.all_completions m hm')

theorem certified_child_bound (mv : Move)
    (hmv : mv ∈ certifiedChildren) (m : Machine)
    (hm : compatible (child mv) m) :
    WeightedBound 7014 m := by
  simp [certifiedChildren] at hmv
  rcases hmv with h | h | h | h | h
  · cases h
    exact child_0RD_bound m hm
  · cases h
    exact child_0LC_bound m hm
  · cases h
    exact child_1RC_bound m hm
  · cases h
    exact child_1RD_bound m hm
  · cases h
    exact child_0RE_bound m hm

/-- The parent cut now has fifteen explicit unresolved children rather than
    twenty. Every removed child is covered by a source-audited certificate. -/
theorem parent_dichotomy_after_five (m : Machine)
    (hm : compatible parent m) :
    WeightedBound 7014 m ∨
      ∃ mv ∈ residual, compatible (child mv) m := by
  rcases parent_dichotomy m hm with hb | ⟨mv, hrem, hc⟩
  · exact Or.inl hb
  · by_cases hcert : mv ∈ certifiedChildren
    · exact Or.inl (certified_child_bound mv hcert m hc)
    · have hdec : decide (mv ∈ certifiedChildren) = false :=
        of_decide_eq_false hcert
      have hkeep : !(decide (mv ∈ certifiedChildren)) = true := by
        simp [hdec]
      exact Or.inr ⟨mv, List.mem_filter.mpr ⟨hrem, hkeep⟩, hc⟩

#print axioms certifiedChildren_count
#print axioms residual_count
#print axioms parent_dichotomy_after_five

end BB6.Agent10Raw108Graft
