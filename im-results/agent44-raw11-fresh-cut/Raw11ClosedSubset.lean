import CanonicalPartial

namespace BB6.Agent44Raw11
open BB6Coverage

/-- A total transition subsystem containing A is enough for nonhalting,
    even if the other rows of the six-state table are unassigned. -/
theorem closedSubset_never (p : PartialMachine) (k : Nat)
    (hpos : 0 < k)
    (h : ∀ q : Fin 6, q.val < k → ∀ b : Bool,
      ∃ mv : Move, p (q,b) = some (some mv) ∧ mv.next.val < k)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  have live (n : Nat) : ∃ c, run m n blank = some c ∧ c.state.val < k := by
    induction n with
    | zero => exact ⟨blank, rfl, hpos⟩
    | succ n ih =>
      obtain ⟨c,hc,hq⟩ := ih
      obtain ⟨mv,hp,hn⟩ := h c.state hq (c.tape c.head)
      refine ⟨applyMove c mv, ?_, hn⟩
      rw [run,hc]
      simp [rawStep,hm _ _ hp]
  intro n
  obtain ⟨c,hc,_⟩ := live n
  change (run m n blank).isSome = true
  rw [hc]
  rfl

/-- Computable premise for the preceding lemma. -/
def closedSubsetOK (p : PartialMachine) (k : Nat) : Bool :=
  (List.finRange 6).all fun q =>
    if q.val < k then [false,true].all fun b =>
      match p (q,b) with
      | some (some mv) => decide (mv.next.val < k)
      | _ => false
    else true

theorem closedSubsetOK_never (p : PartialMachine) (k : Nat) (hpos : 0 < k)
    (h : closedSubsetOK p k = true) : ∀ m, compatible p m → NeverHalts m := by
  apply closedSubset_never p k hpos
  intro q hq b
  have hq' := List.all_eq_true.mp h q (List.mem_finRange q)
  rw [ite_eq_left hq] at hq'
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hh := List.all_eq_true.mp hq' b hb
  cases he : p (q,b) with
  | none => simp [he] at hh
  | some t =>
    cases t with
    | none => simp [he] at hh
    | some mv => exact ⟨mv,rfl,by simpa [he] using hh⟩

#print axioms closedSubsetOK_never
end BB6.Agent44Raw11
