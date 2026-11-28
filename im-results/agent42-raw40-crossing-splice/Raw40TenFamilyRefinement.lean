import Raw40SevenFamilyRefinement
import Raw40A0LB
import Raw40A0RB
import Raw40A1RB

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40TenFamilyRefinement
open BB6Coverage BB6.Agent47CanonicalFrontier

def inA0LB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0LB.bounds.any fun x =>
    BB6.Agent19Raw40.A0LB.equalTable e.2 (BB6.Agent19Raw40.A0LB.child x.1)

def inA0RB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0RB.bounds.any fun x =>
    BB6.Agent19Raw40.A0RB.equalTable e.2 (BB6.Agent19Raw40.A0RB.child x.1)

def inA1RB (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1RB.bounds.any fun x =>
    BB6.Agent19Raw40.A1RB.equalTable e.2 (BB6.Agent19Raw40.A1RB.child x.1)

/-- Raw40's canonical five-hole frontier after composing the ten
    deeply-developed six-hole first-query families. -/
def remaining : List (List Move × PartialMachine) :=
  BB6.Agent42Raw40SevenFamilyRefinement.remaining.filter fun e =>
    !(inA0LB e || inA0RB e || inA1RB e)

/-- The ten composed first-query families cover 114 of Raw40's 189
    canonical five-hole residuals. -/
theorem count : remaining.length = 75 := by decide

theorem sound :
    ∀ m, TNFQuotientCompatible BB6.Agent19Raw40.parent m →
      WeightedBound 75493794 m ∨
        ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent42Raw40SevenFamilyRefinement.sound m hm with hb | ⟨e,he,hq⟩
  · left
    intro n d hn hd
    exact Nat.le_trans (hb n d hn hd) (by omega)
  · by_cases h0 : inA0LB e = true
    · left
      unfold inA0LB at h0
      obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h0
      have eq : e.2 = BB6.Agent19Raw40.A0LB.child x.1 :=
        BB6.Agent19Raw40.A0LB.equalTable_sound _ _ heq
      have hb := BB6.Agent19Raw40.A0LB.children x hx m (eq ▸ hq)
      have hB : x.2 ≤ 75493794 :=
        of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A0LB.boundOK x hx)
      intro n d hn hd
      exact Nat.le_trans (hb n d hn hd) hB
    · by_cases h1 : inA0RB e = true
      · left
        unfold inA0RB at h1
        obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h1
        have eq : e.2 = BB6.Agent19Raw40.A0RB.child x.1 :=
          BB6.Agent19Raw40.A0RB.equalTable_sound _ _ heq
        have hb := BB6.Agent19Raw40.A0RB.children x hx m (eq ▸ hq)
        have hB : x.2 ≤ 637 :=
          of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A0RB.boundOK x hx)
        intro n d hn hd
        exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
      · by_cases h2 : inA1RB e = true
        · left
          unfold inA1RB at h2
          obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h2
          have eq : e.2 = BB6.Agent19Raw40.A1RB.child x.1 :=
            BB6.Agent19Raw40.A1RB.equalTable_sound _ _ heq
          have hb := BB6.Agent19Raw40.A1RB.children x hx m (eq ▸ hq)
          have hB : x.2 ≤ 1130 :=
            of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A1RB.boundOK x hx)
          intro n d hn hd
          exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
        · right
          have h0f : inA0LB e = false := by
            cases hx : inA0LB e
            · rfl
            · exact (h0 hx).elim
          have h1f : inA0RB e = false := by
            cases hx : inA0RB e
            · rfl
            · exact (h1 hx).elim
          have h2f : inA1RB e = false := by
            cases hx : inA1RB e
            · rfl
            · exact (h2 hx).elim
          refine ⟨e, ?_, hq⟩
          simp [remaining, he, h0f, h1f, h2f]

#print axioms count
#print axioms sound
end BB6.Agent42Raw40TenFamilyRefinement
