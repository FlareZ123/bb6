import Raw40CanonicalCut
import Raw40A0LAExact
import Raw40A0RC
import Raw40A0RD
import Raw40A1LA
import Raw40A1RC

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42Raw40FiveFamilyRefinement
open BB6Coverage BB6.Agent47CanonicalFrontier

def inA0LA (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0LA.bounds.any fun x =>
    BB6.Agent19Raw40.A0LA.equalTable e.2 (BB6.Agent19Raw40.A0LA.child x.1)

def inA0RC (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0RC.bounds.any fun x =>
    BB6.Agent19Raw40.A0RC.equalTable e.2 (BB6.Agent19Raw40.A0RC.child x.1)

def inA0RD (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A0RD.bounds.any fun x =>
    BB6.Agent19Raw40.A0RD.equalTable e.2 (BB6.Agent19Raw40.A0RD.child x.1)

def inA1LA (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1LA.bounds.any fun x =>
    BB6.Agent19Raw40.A1LA.equalTable e.2 (BB6.Agent19Raw40.A1LA.child x.1)

def inA1RC (e : List Move × PartialMachine) : Bool :=
  BB6.Agent19Raw40.A1RC.bounds.any fun x =>
    BB6.Agent19Raw40.A1RC.equalTable e.2 (BB6.Agent19Raw40.A1RC.child x.1)

def solved (e : List Move × PartialMachine) : Bool :=
  inA0LA e || inA0RC e || inA0RD e || inA1LA e || inA1RC e

/-- Raw40's two-level canonical frontier after composing five complete
    six-hole first-query families. -/
def remaining : List (List Move × PartialMachine) :=
  BB6.Agent19Raw40.canonicalRemaining.filter fun e => ! solved e

/-- 57 of Raw40's 189 canonical five-hole residuals lie in the five
    completely solved first-query families. -/
theorem count : remaining.length = 132 := by decide

theorem sound :
    ∀ m, TNFQuotientCompatible BB6.Agent19Raw40.parent m →
      WeightedBound 22169 m ∨
        ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent19Raw40.canonical_local_sound m hm with hb | ⟨e,he,hq⟩
  · left
    intro n d hn hd
    exact Nat.le_trans (hb n d hn hd) (by omega)
  · by_cases h0 : inA0LA e = true
    · left
      unfold inA0LA at h0
      obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h0
      have eq : e.2 = BB6.Agent19Raw40.A0LA.child x.1 :=
        BB6.Agent19Raw40.A0LA.equalTable_sound _ _ heq
      have hb := BB6.Agent42Raw40A0LAExact.children x hx m (eq ▸ hq)
      have hB : x.2 ≤ 22169 :=
        of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A0LA.boundOK x hx)
      intro n d hn hd
      exact Nat.le_trans (hb n d hn hd) hB
    · by_cases h1 : inA0RC e = true
      · left
        unfold inA0RC at h1
        obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h1
        have eq : e.2 = BB6.Agent19Raw40.A0RC.child x.1 :=
          BB6.Agent19Raw40.A0RC.equalTable_sound _ _ heq
        have hb := BB6.Agent19Raw40.A0RC.children x hx m (eq ▸ hq)
        have hB : x.2 ≤ 888 :=
          of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A0RC.boundOK x hx)
        intro n d hn hd
        exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
      · by_cases h2 : inA0RD e = true
        · left
          unfold inA0RD at h2
          obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h2
          have eq : e.2 = BB6.Agent19Raw40.A0RD.child x.1 :=
            BB6.Agent19Raw40.A0RD.equalTable_sound _ _ heq
          have hb := BB6.Agent19Raw40.A0RD.children x hx m (eq ▸ hq)
          have hB : x.2 ≤ 1132 :=
            of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A0RD.boundOK x hx)
          intro n d hn hd
          exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
        · by_cases h3 : inA1LA e = true
          · left
            unfold inA1LA at h3
            obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h3
            have eq : e.2 = BB6.Agent19Raw40.A1LA.child x.1 :=
              BB6.Agent19Raw40.A1LA.equalTable_sound _ _ heq
            have hb := BB6.Agent19Raw40.A1LA.children x hx m (eq ▸ hq)
            have hB : x.2 ≤ 790 :=
              of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A1LA.boundOK x hx)
            intro n d hn hd
            exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
          · by_cases h4 : inA1RC e = true
            · left
              unfold inA1RC at h4
              obtain ⟨x,hx,heq⟩ := List.any_eq_true.mp h4
              have eq : e.2 = BB6.Agent19Raw40.A1RC.child x.1 :=
                BB6.Agent19Raw40.A1RC.equalTable_sound _ _ heq
              have hb := BB6.Agent19Raw40.A1RC.children x hx m (eq ▸ hq)
              have hB : x.2 ≤ 5729 :=
                of_decide_eq_true (List.all_eq_true.mp BB6.Agent19Raw40.A1RC.boundOK x hx)
              intro n d hn hd
              exact Nat.le_trans (hb n d hn hd) (Nat.le_trans hB (by omega))
            · right
              have h0f : inA0LA e = false := by
                cases hx : inA0LA e
                · rfl
                · exact (h0 hx).elim
              have h1f : inA0RC e = false := by
                cases hx : inA0RC e
                · rfl
                · exact (h1 hx).elim
              have h2f : inA0RD e = false := by
                cases hx : inA0RD e
                · rfl
                · exact (h2 hx).elim
              have h3f : inA1LA e = false := by
                cases hx : inA1LA e
                · rfl
                · exact (h3 hx).elim
              have h4f : inA1RC e = false := by
                cases hx : inA1RC e
                · rfl
                · exact (h4 hx).elim
              refine ⟨e, ?_, hq⟩
              simp [remaining, solved, he, h0f, h1f, h2f, h3f, h4f]

#print axioms count
#print axioms sound
end BB6.Agent42Raw40FiveFamilyRefinement
