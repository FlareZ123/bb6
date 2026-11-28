import CanonicalPartial
set_option maxRecDepth 100000

namespace BB6.Agent4Raw56Root
open BB6Coverage BB6.Agent19CanonicalPartial BB6.Agent47PartialAudit

/-- To show that a certified audit has no residual machines outside a fixed
    list, it is enough to prove the inclusion for each successor.  Unlike
    an exact residual-trace equation, this lemma does not elaborate or
    normalize the entire concatenated list at the parent. -/
theorem canonicalResiduals_split_subset
    (p : PartialMachine) (cut n : Nat) (s : Slot)
    (kids : Move → PartialAudit) (allowed : List PartialMachine)
    (hchild : ∀ mv : Move,
      ∀ e ∈ canonicalResiduals (refine p s (some mv))
          (max cut (mv.next.val+1)) (kids mv), e.2 ∈ allowed) :
    ∀ e ∈ canonicalResiduals p cut (.split n s kids), e.2 ∈ allowed := by
  intro e he
  simp only [canonicalResiduals] at he
  obtain ⟨mv, _, hmap⟩ := List.mem_flatMap.mp he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmap
  simpa using hchild mv x hx

#print axioms canonicalResiduals_split_subset
end BB6.Agent4Raw56Root
