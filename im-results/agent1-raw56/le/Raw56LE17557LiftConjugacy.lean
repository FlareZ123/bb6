import Raw56LE17557FrameMachine
import Raw56LE17557DefectStack
import Raw56LE17557RankedTriads

namespace BB6.Agent1Raw56.LE17557LiftConjugacy
open BB6.Agent1Raw56.LE17557FrameSchedule
open BB6.Agent1Raw56.LE17557ActionGrammar
open BB6.Agent1Raw56.LE17557FrameMachine
open BB6.Agent1Raw56.LE17557DefectStack

/-- Refinement converts each low B hit of cost 7 into the lifted BBA block of
    cost 15, while carries keep cost 1.  Hence low-cost after one action-word
    lift is exactly the high-side cost before the lift. -/
theorem lowCost_refine_eq_highCost (w : List Bool) :
    lowCost (refine w) = highCost w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [refine_cons, lowCost_append, ih]
      cases a <;>
        simp [refineLetter, lowCost, highCost, countB, countC,
          List.count_append] <;> omega

/-- A pure B/C hit word has an outer trace with no nested-frame assumptions. -/
theorem hitWord_outerTraceBelow_zero (w : List Bool) :
    OuterTraceBelow 0 (hitWord w) w := by
  induction w with
  | nil => exact .nil
  | cons a w ih =>
      cases a with
      | false =>
          simpa [hitWord, hitAction] using
            (OuterTraceBelow.hitC (k := 0) ih)
      | true =>
          simpa [hitWord, hitAction] using
            (OuterTraceBelow.hitB (k := 0) ih)

theorem refine_cons_ne_nil (a : Bool) (w : List Bool) :
    refine (a :: w) ≠ [] := by
  cases a <;> simp [refine, refineLetter]

/-- One substitution level is an exact abstract conjugacy for every nonempty
    outer hit word: the lifted high-side action word consumes precisely the
    high-side runway corresponding to the low word, including all inserted
    rank-0 frames from lifted carries. -/
theorem lift_hitWord_consumes_highCost
    (a : Bool) (w : List Bool) (st : List Nat) :
    execLow (lift (hitWord (a :: w))) (highCost (a :: w) :: st) =
      some st := by
  have htrace :=
    outerTraceBelow_lift (hitWord_outerTraceBelow_zero (a :: w))
  have hsem := outerTraceBelow_exec htrace
    (closed := by
      intro r hr st'
      exact segment_closes_low r st')
    (highCost (a :: w) :: st)
  rw [hsem]
  rw [← lowCost_refine_eq_highCost]
  have hn := refine_cons_ne_nil a w
  cases hrf : refine (a :: w) with
  | nil => exact False.elim (hn hrf)
  | cons b bs =>
      simpa [hrf] using hitWord_consumes_own_cost b bs st

/-- The low and high runway sizes of a rank-r frame are exactly the zero-weight
    pair in the weighted defect relation. -/
theorem frame_costs_related (r : Nat) :
    weightedZero (lowCost (frame r)) 0 = highCost (frame r) := by
  have h := frame_prefix_defect r (p := []) (s := frame r) (by simp)
  have hl := lowRemaining_eq_suffixCost r
    (p := []) (s := frame r) (by simp)
  have hh := highRemaining_eq_suffixCost r
    (p := []) (s := frame r) (by simp)
  rw [hl, hh] at h
  simpa [prefixWeight] using h

/-- Pushing an exact frame preserves the weighted low/high stack relation with
    zero initial defect weight. -/
theorem push_frame_related {low weights high : List Nat}
    (h : DefectStack low weights high) (r : Nat) :
    DefectStack
      (lowCost (frame r) :: low)
      (0 :: weights)
      (highCost (frame r) :: high) := by
  have hz : rhoZero (lowCost (frame r)) = highCost (frame r) := by
    simpa using frame_costs_related r
  simpa [hz] using push_zero h (lowCost (frame r))

/-- Every recursive frame closes on both scales.  On the high side this is not
    a separate bounded replay: it follows uniformly from the exact action-word
    lift and strict-rank closure of inserted nested frames. -/
theorem frame_pair_closes (r : Nat) (lowTail highTail : List Nat) :
    execLow (hitWord (frame r))
        (lowCost (frame r) :: lowTail) = some lowTail ∧
    execLow (lift (hitWord (frame r)))
        (highCost (frame r) :: highTail) = some highTail := by
  have hn := frame_nonempty r
  cases hf : frame r with
  | nil => exact False.elim (hn hf)
  | cons a w =>
      constructor
      · simpa [hf] using hitWord_consumes_own_cost a w lowTail
      · simpa [hf] using lift_hitWord_consumes_highCost a w highTail

/-- A related pair of stacks may therefore push the rank-r frame, execute the
    low word and its one-level lifted high word, and return to the original
    related tails.  This is the abstract frame-level conjugacy needed by the
    source synchronization proof for leaf 17557. -/
theorem frame_conjugate_cycle {low weights high : List Nat}
    (h : DefectStack low weights high) (r : Nat) :
    DefectStack
      (lowCost (frame r) :: low)
      (0 :: weights)
      (highCost (frame r) :: high) ∧
    execLow (hitWord (frame r))
      (lowCost (frame r) :: low) = some low ∧
    execLow (lift (hitWord (frame r)))
      (highCost (frame r) :: high) = some high := by
  exact ⟨push_frame_related h r,
    (frame_pair_closes r low high).1,
    (frame_pair_closes r low high).2⟩

#print axioms lowCost_refine_eq_highCost
#print axioms hitWord_outerTraceBelow_zero
#print axioms lift_hitWord_consumes_highCost
#print axioms frame_costs_related
#print axioms push_frame_related
#print axioms frame_pair_closes
#print axioms frame_conjugate_cycle
end BB6.Agent1Raw56.LE17557LiftConjugacy
