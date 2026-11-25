import Frontier

namespace BB6.Agent46StateClosure
open BB6Coverage

/-- A finite, ordinary, forward-closed set of states containing A. No tape
    observation or bounded-run assumption is used. -/
def stateCheck (p : PartialMachine) (mask : Nat) : Bool :=
  mask.testBit 0 && (List.finRange 6).all fun q =>
    if mask.testBit q.val then [false, true].all fun b =>
      match p (q,b) with
      | some (some mv) => mask.testBit mv.next.val
      | _ => false
    else true

theorem stateCheck_sound (p : PartialMachine) (mask : Nat)
    (h : stateCheck p mask = true) : ∀ m, compatible p m → NeverHalts m := by
  have hc : mask.testBit 0 = true ∧
      (List.finRange 6).all (fun q => if mask.testBit q.val then
        [false, true].all (fun b => match p (q,b) with
          | some (some mv) => mask.testBit mv.next.val
          | _ => false) else true) = true := by
    simpa only [stateCheck, Bool.and_eq_true] using h
  intro m hm
  have stepClosed : ∀ c : Config, mask.testBit c.state.val = true →
      ∃ d, rawStep m c = some d ∧ mask.testBit d.state.val = true := by
    intro c hq
    have hh := List.all_eq_true.mp hc.2 c.state (List.mem_finRange c.state)
    simp only [hq, ite_true] at hh
    have hb : c.tape c.head ∈ [false,true] := by cases c.tape c.head <;> simp
    have hrow := List.all_eq_true.mp hh (c.tape c.head) hb
    cases hr : p (readSlot c) with
    | none => simp [hr] at hrow
    | some v =>
      cases v with
      | none => simp [hr] at hrow
      | some mv =>
        have hmv := hm (readSlot c) (some mv) hr
        exact ⟨applyMove c mv, by simp [rawStep, hmv], by
          change mask.testBit mv.next.val = true
          simpa only [hr] using hrow⟩
  have allLive : ∀ n, ∃ c, run m n blank = some c ∧ mask.testBit c.state.val = true := by
    intro n
    induction n with
    | zero => exact ⟨blank,rfl,hc.1⟩
    | succ n ih =>
      obtain ⟨c,hr,hq⟩ := ih
      obtain ⟨d,hs,hd⟩ := stepClosed c hq
      exact ⟨d, by simp [run,hr,hs],hd⟩
  intro n
  obtain ⟨c,hc,_⟩ := allLive n
  rw [hc]
  rfl

#print axioms stateCheck_sound
end BB6.Agent46StateClosure
