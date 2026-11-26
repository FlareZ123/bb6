import Agent46CanonicalCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46CanonicalCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole

/-- Whether every canonical branch is certified, independent of table data. -/
def closedCut (cut : Nat) : Cut → Bool
  | .unresolved => false
  | .closed _ => true
  | .bounded _ _ _ => true
  | .state _ => true
  | .split _ _ kids => allMoves (fun mv =>
      if mv.next.val ≤ cut then closedCut (nextCut cut mv) (kids mv) else true)
termination_by structural t => t

theorem residuals_empty_of_closedCut {p : PartialMachine} {cut : Nat} {t : Cut}
    (h : closedCut cut t = true) : residuals p cut t = [] := by
  induction t generalizing p cut with
  | unresolved => simp [closedCut] at h
  | closed _ => rfl
  | bounded _ _ _ => rfl
  | state _ => rfl
  | split n s kids ih =>
    simp only [closedCut] at h
    simp only [residuals]
    have hall : ∀ mv ∈ moves.filter (fun mv => decide (mv.next.val ≤ cut)),
        (residuals (refine p s (some mv)) (nextCut cut mv) (kids mv)).map
          (fun e => (mv :: e.1,e.2)) = [] := by
      intro mv hmv
      have hv : mv.next.val ≤ cut := of_decide_eq_true (List.mem_filter.mp hmv).2
      have hc := allMoves_sound _ h mv
      rw [if_pos hv] at hc
      rw [ih mv hc]
      rfl
    exact List.flatMap_eq_nil_iff.mpr hall

#print axioms residuals_empty_of_closedCut
end BB6.Agent46CanonicalCut
