import WeightedFirstOneCover
import WeightedNonhaltLeafAdapter

set_option maxRecDepth 12000
set_option maxHeartbeats 0
namespace BB6.Agent8TNFPath
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt

def advanceCut (cut : Nat) (mv : Move) : Nat :=
  if mv.next.val = cut then cut+1 else cut

/-- Reachability in the full first-hole TNF expansion, before optional
    decider pruning. Each edge uses the actual blank-start trace. -/
inductive FirstHolePath : PartialMachine → Nat → Prop where
  | root : FirstHolePath BB6.CoverageAdapter.firstOneCylinder 2
  | step {p cut n c mv}
      (parent : FirstHolePath p cut)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none)
      (hslot : (readSlot c).1.val < cut)
      (hmove : mv.next.val ≤ cut) :
      FirstHolePath (refine p (readSlot c) (some mv)) (advanceCut cut mv)

/-- Verify an endpoint without requiring decidable equality of functions. -/
def endpointCheck (m : Machine) (p : PartialMachine) (cut : Nat) : Bool :=
  decide (cut = 6) && ((List.finRange 6).all fun q =>
    [false, true].all fun b => decide (p (q,b) = forgetHaltRows m (q,b)))

/-- The schedule records only time and queried row. Moves are obtained from
    the target table, so a witness cannot silently select a different action.
    A query is accepted only if all preceding moves were known in the parent
    and the current row is unassigned. -/
def pathCheck (m : Machine) (p : PartialMachine) (cut : Nat) : List (Nat × Slot) → Bool
  | [] => endpointCheck m p cut
  | (n,s) :: rest =>
    match m s with
    | none => false
    | some mv =>
      decide (p s = none) && (decide ((knownRun p n).map readSlot = some s) &&
        (decide (s.1.val < cut) && (decide (mv.next.val ≤ cut) &&
          pathCheck m (refine p s (some mv)) (advanceCut cut mv) rest)))

theorem endpointCheck_sound (m : Machine) (p : PartialMachine) (cut : Nat)
    (h : endpointCheck m p cut = true) : cut = 6 ∧ p = forgetHaltRows m := by
  simp only [endpointCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  funext s
  rcases s with ⟨q,b⟩
  have hq := List.all_eq_true.mp h.2 q (List.mem_finRange q)
  have hb : b ∈ [false, true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq b hb)

theorem pathCheck_sound (m : Machine) (p : PartialMachine) (cut : Nat)
    (xs : List (Nat × Slot)) (hp : FirstHolePath p cut)
    (h : pathCheck m p cut xs = true) : FirstHolePath (forgetHaltRows m) 6 := by
  induction xs generalizing p cut with
  | nil =>
    have ⟨hcut, heq⟩ := endpointCheck_sound m p cut h
    rw [← hcut, ← heq]
    exact hp
  | cons x xs ih =>
    rcases x with ⟨n,s⟩
    cases hm : m s with
    | none => simp [pathCheck, hm] at h
    | some mv =>
      simp only [pathCheck, hm, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hhole, hread, hslot, hmove, htail⟩ := h
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
        have hs : readSlot c = s := by simpa [hr] using hread
        subst s
        exact ih _ _ (FirstHolePath.step hp hr hhole hslot hmove) htail

theorem checked_from_root (m : Machine) (xs : List (Nat × Slot))
    (h : pathCheck m BB6.CoverageAdapter.firstOneCylinder 2 xs = true) :
    FirstHolePath (forgetHaltRows m) 6 :=
  pathCheck_sound m _ _ xs FirstHolePath.root h

#print axioms endpointCheck_sound
#print axioms pathCheck_sound
#print axioms checked_from_root
end BB6.Agent8TNFPath
