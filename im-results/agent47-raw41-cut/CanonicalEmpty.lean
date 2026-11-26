import CanonicalPartial

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19CanonicalPartial
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath

/-- Checking that a canonical tree has no residuals requires no table replay.
The omitted fresh-state aliases are handled by exactly the canonical checker guard. -/
def noResidual (cut : Nat) (t : PartialAudit) : Bool :=
  match t with
  | .unresolved => false
  | .closed _ => true
  | .split _ _ kids => allMoves (fun mv => if mv.next.val ≤ cut then noResidual (max cut (mv.next.val+1)) (kids mv) else true)
termination_by structural t

theorem noResidual_sound (p : PartialMachine) (cut : Nat) (t : PartialAudit) (h : noResidual cut t = true) : canonicalResiduals p cut t = [] := by
  induction t generalizing p cut with
  | unresolved => simp [noResidual] at h
  | closed a => rfl
  | split n s kids ih =>
    rw [canonicalResiduals]
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    obtain ⟨mv, hm, he⟩ := List.mem_flatMap.mp he
    have hmv : mv.next.val ≤ cut := of_decide_eq_true (List.mem_filter.mp hm).2
    have hk := allMoves_sound _ h mv
    simp only [if_pos hmv] at hk
    have hz := ih mv (refine p s (some mv)) (max cut (mv.next.val+1)) hk
    rw [hz] at he
    simp at he
#print axioms noResidual_sound
end BB6.Agent19CanonicalPartial
