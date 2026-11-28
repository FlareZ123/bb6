import Raw40CanonicalCut
import Raw40A0LAExact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40A0LARefinement
open BB6Coverage BB6.Agent47CanonicalFrontier
/-- Detect exactly the twelve five-hole residual tables under Raw40's
    A1=0LA branch. -/
def inA0LA (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0LA.bounds.any (fun x => BB6.Agent19Raw40.A0LA.equalTable e.2 (BB6.Agent19Raw40.A0LA.child x.1))

/-- Raw40's two-level canonical residual frontier after discharging the
    complete A1=0LA branch. -/
def remaining : List (List Move × PartialMachine) :=
  BB6.Agent19Raw40.canonicalRemaining.filter (fun e => ! inA0LA e)

theorem count : remaining.length = 177 := by decide

/-- The Raw40 parent now has a 177-residual conditional frontier at the
    sharp A1=0LA local bound 22169. -/
theorem sound :
    ∀ m, TNFQuotientCompatible BB6.Agent19Raw40.parent m →
      WeightedBound 22169 m ∨
        ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent19Raw40.canonical_local_sound m hm with hb | ⟨e,he,hq⟩
  · left
    intro n d hn hd
    exact Nat.le_trans (hb n d hn hd) (by omega)
  · by_cases h : inA0LA e = true
    · left
      unfold inA0LA at h
      obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h
      have eq : e.2 = BB6.Agent19Raw40.A0LA.child x.1 := BB6.Agent19Raw40.A0LA.equalTable_sound _ _ heq
      have hb := BB6.Agent42Raw40A0LAExact.children x hx m (eq ▸ hq)
      have hB : x.2 ≤ 22169 :=
        of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A0LA.boundOK x hx)
      intro n d hn hd
      exact Nat.le_trans (hb n d hn hd) hB
    · right
      have hf : inA0LA e = false := by
        cases heq : inA0LA e
        · rfl
        · exact (h heq).elim
      refine ⟨e, ?_, hq⟩
      simp [remaining, he, hf]

#print axioms count
#print axioms sound
end BB6.Agent42Raw40A0LARefinement
