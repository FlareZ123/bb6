import SingletonFrontier

namespace BB6Coverage

private theorem sparse_refine (m : Machine) (seen : List Slot)
    (s : Slot) (_hs : s ∉ seen) :
    refine (sparseOfSeen m seen) s (m s) = sparseOfSeen m (s :: seen) := by
  funext q
  by_cases hq : q = s
  · subst q
    simp [refine, sparseOfSeen]
  · simp [refine, sparseOfSeen, hq]

/-- Graft any authentic sparse-cylinder certificate into the global search
with all alternative 25-way branch choices left explicitly unresolved. -/
private noncomputable def cylinderFrom
    (good : Machine → Prop) (m : Machine) (fixed : List Slot)
    (hg : Cover good (sparseOfSeen m fixed))
    (seen remaining : List Slot)
    (hnd : remaining.Nodup)
    (hdisj : ∀ s, s ∈ remaining → s ∉ seen)
    (hcover : ∀ s, (s ∈ seen ∨ s ∈ remaining) ↔ s ∈ fixed) :
    FrontierAudit good (sparseOfSeen m seen) := by
  induction remaining generalizing seen with
  | nil =>
      have hmem : ∀ s, s ∈ seen ↔ s ∈ fixed := by
        intro s
        simpa using hcover s
      have heq : sparseOfSeen m seen = sparseOfSeen m fixed := by
        funext s
        simp [sparseOfSeen, hmem s]
      rw [heq]
      exact .certified _ hg
  | cons s rest ih =>
      have hnd2 : s ∉ rest ∧ rest.Nodup := List.nodup_cons.mp hnd
      have hs : s ∉ seen := hdisj s (by simp)
      apply FrontierAudit.branch (sparseOfSeen m seen) s (by simp [sparseOfSeen, hs])
      intro t ht
      by_cases ht0 : t = m s
      · subst t
        have hdisj2 : ∀ q, q ∈ rest → q ∉ s :: seen := by
          intro q hq hbad
          rcases List.mem_cons.mp hbad with hqs | hseen
          · subst q
            exact hnd2.1 hq
          · exact hdisj q (by simp [hq]) hseen
        have hcover2 : ∀ q, (q ∈ s :: seen ∨ q ∈ rest) ↔ q ∈ fixed := by
          intro q
          have hc := hcover q
          simpa only [List.mem_cons, or_assoc, or_comm, or_left_comm] using hc
        have child := ih (s :: seen) hnd2.2 hdisj2 hcover2
        simpa only [sparse_refine m seen s hs] using child
      · exact FrontierAudit.unresolved _

/-- Every full twelve-slot machine falls into a certified cylinder or a
disjoint open cylinder. Only the pinned fixed slots are branched on; all
other transitions remain arbitrary at the one certified terminal. -/
noncomputable def cylinderGlobal
    (good : Machine → Prop) (m : Machine) (fixed : List Slot)
    (hnd : fixed.Nodup)
    (hg : Cover good (sparseOfSeen m fixed)) :
    FrontierAudit good emptyTable := by
  have h := cylinderFrom good m fixed hg [] fixed hnd
    (by simp)
    (fun s => by simp)
  have heq : sparseOfSeen m [] = emptyTable := by
    funext s
    simp [sparseOfSeen, emptyTable]
  rw [← heq]
  exact h

#print axioms cylinderGlobal
end BB6Coverage
