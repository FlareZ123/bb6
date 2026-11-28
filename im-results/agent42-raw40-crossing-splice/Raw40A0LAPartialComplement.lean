import Raw40A0LABase

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LAPartialComplement
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
open BB6.Agent19Raw40.A0LA

/-- The live Raw40 A1=0LA six-hole complement after *any* chosen subset
    of its twelve source-reconstructed five-hole children has been closed.
    Unlike the existing all-twelve conditional consumer, this theorem can
    be instantiated immediately when just one child is source-accepted. -/
theorem partial_close (solved : List Move)
    (hs : ∀ e ∈ bounds, e.1 ∈ solved →
      ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 22169 m ∨
      ∃ e ∈ bounds, e.1 ∉ solved ∧ TNFQuotientCompatible (child e.1) m := by
  intro m hm
  rcases canonicalSound 22169 p 4 tree (by decide) supported root nohalt checked m hm with
    hb | ⟨leaf,hleaf,hquot⟩
  · exact Or.inl hb
  · have hh := List.all_eq_true.mp partition leaf hleaf
    obtain ⟨e,he,heq⟩ := List.any_eq_true.mp hh
    have eq := equalTable_sound _ _ heq
    have hchild : TNFQuotientCompatible (child e.1) m := eq ▸ hquot
    by_cases hsolved : e.1 ∈ solved
    · left
      have hc := hs e he hsolved m hchild
      have hb' : e.2 ≤ 22169 :=
        of_decide_eq_true (List.all_eq_true.mp boundOK e he)
      intro k d hk hd
      exact Nat.le_trans (hc k d hk hd) hb'
    · exact Or.inr ⟨e,he,hsolved,hchild⟩

/-- Four historically locally kernel-accepted C1 child families:
    0LB (Round5), 1LB (Round4), 0RB (Round8), 1RC (Round6).
    Their 8-child complement is an exact finite roster. The theorem
    below states the proof interface explicitly without silently assuming
    these old accepted artifacts were recompiled at today's revision. -/
def firstFour : List Move :=
  [⟨false,false,1⟩,⟨true,false,1⟩,⟨false,true,1⟩,⟨true,true,2⟩]

def remainingEight : List (Move × Nat) :=
  bounds.filter fun e => decide (e.1 ∉ firstFour)

theorem remainingEight_count : remainingEight.length = 8 := by decide

theorem after_firstFour
    (h : ∀ e ∈ bounds, e.1 ∈ firstFour →
      ∀ m, TNFQuotientCompatible (child e.1) m → WeightedBound e.2 m) :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 22169 m ∨
      ∃ e ∈ remainingEight, TNFQuotientCompatible (child e.1) m := by
  intro m hm
  rcases partial_close firstFour h m hm with hb | ⟨e,he,hn,hq⟩
  · exact Or.inl hb
  · right
    refine ⟨e,?_,hq⟩
    simp only [remainingEight,List.mem_filter]
    exact ⟨he,by exact decide_eq_true hn⟩

#print axioms partial_close
#print axioms after_firstFour
end BB6.Agent42Raw40A0LAPartialComplement
