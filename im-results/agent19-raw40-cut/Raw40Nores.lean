import CanonicalPartial
set_option maxRecDepth 100000
namespace BB6.Agent19CanonicalPartial
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier

theorem noresSplit (p : PartialMachine) (cut n : Nat) (s : Slot) (kids : Move → PartialAudit)
    (h : ∀ mv : Move, mv.next.val ≤ cut →
      canonicalResiduals (refine p s (some mv)) (max cut (mv.next.val+1)) (kids mv) = []) :
    canonicalResiduals p cut (.split n s kids) = [] := by
  simp only [canonicalResiduals]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  obtain ⟨mv,hm,he'⟩ := List.mem_flatMap.mp he
  have hle : mv.next.val ≤ cut := by
    have hx := (List.mem_filter.mp hm).2
    exact of_decide_eq_true hx
  rw [h mv hle] at he'
  simp at he'

#print axioms noresSplit
end BB6.Agent19CanonicalPartial
