import Raw40LocalCut
import Raw40RE1REExact
import Raw40C0RC1RDAll
import Raw40C0RC0LAAll
import Raw40C0RB1LCAll
import Raw40C1LC1LCAll
import Raw40C0RB0LAAll
import Raw40C0RC1LAAll
import Raw40C0RC0RDAll
import Raw40C0RC1RBAll
import Raw40C0LB1LCAll
import Raw40C0LB1RCAll
import Raw40C1RB1RCAll
import Raw40C0RD1RCAll
import Raw40C1RB0LAAll
import Raw40C0RC1LCAll
import Raw40C0RE0REAll
import Raw40C1RC1RBAll
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40.Raw40NewClosed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier

def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun s => [false,true].all fun b => decide (p (s,b)=q (s,b))

theorem equalTable_sound (p q : PartialMachine) (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨q',b⟩
  have hq := List.all_eq_true.mp h q' (List.mem_finRange q')
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq b hb)

def closed : List PartialMachine :=
  [Raw40RE1RE.p,
   Raw40C0RC1RD.p,
   Raw40C0RC0LA.p,
   Raw40C0RB1LC.p,
   Raw40C1LC1LC.p,
   Raw40C0RB0LA.p,
   Raw40C0RC1LA.p,
   Raw40C0RC0RD.p,
   Raw40C0RC1RB.p,
   Raw40C0LB1LC.p,
   Raw40C0LB1RC.p,
   Raw40C1RB1RC.p,
   Raw40C0RD1RC.p,
   Raw40C1RB0LA.p,
   Raw40C0RC1LC.p,
   Raw40C0RE0RE.p,
   Raw40C1RC1RB.p]

theorem closed_sound : ∀ p ∈ closed, ∀ m, TNFQuotientCompatible p m → WeightedBound 7014 m := by
  intro p hp
  simp only [closed,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · intro m hm k d hk hd; exact Nat.le_trans (RE1REExact.quotient_bound m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RC1RD.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RC0LA.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RB1LC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C1LC1LC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RB0LA.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RC1LA.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RC0RD.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RC1RB.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0LB1LC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0LB1RC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C1RB1RC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RD1RC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C1RB0LA.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RC1LC.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C0RE0RE.all_quotient m hm k d hk hd) (by decide)
  · intro m hm k d hk hd; exact Nat.le_trans (Raw40C1RC1RB.all_quotient m hm k d hk hd) (by decide)

def remaining := canonicalRemaining.filter fun e => !(closed.any (equalTable e.2))

theorem count : remaining.length = 172 := by decide

theorem local_sound : ∀ m, TNFQuotientCompatible parent m → WeightedBound 7014 m ∨
    ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases canonical_local_sound m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hh : closed.any (equalTable e.2) = true
    · obtain ⟨p,hp,heq⟩ := List.any_eq_true.mp hh
      have eq := equalTable_sound e.2 p heq
      exact Or.inl (closed_sound p hp m (eq ▸ hq))
    · exact Or.inr ⟨e,by simp [remaining,he,hh],hq⟩

#print axioms local_sound
#print axioms count
end BB6.Agent19Raw40.Raw40NewClosed
