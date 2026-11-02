import FrontierMass
namespace BB6Coverage

def sparseOfSeen (m : Machine) (seen : List Slot) : PartialMachine :=
  fun slot => if slot ∈ seen then some (m slot) else none

private theorem sparseOfSeen_refine (m : Machine) (seen : List Slot)
    (slot : Slot) (_h : slot ∉ seen) :
    refine (sparseOfSeen m seen) slot (m slot) =
      sparseOfSeen m (slot :: seen) := by
  funext q
  by_cases hq : q = slot
  · subst q
    simp [refine, sparseOfSeen]
  · simp [refine, sparseOfSeen, hq]

private theorem singleCover (good : Machine → Prop) (m : Machine)
    (seen : List Slot) (hseen : ∀ s : Slot, s ∈ seen)
    (hg : good m) : Cover good (sparseOfSeen m seen) := by
  apply Cover.leaf
  intro m' hm'
  have heq : m' = m := by
    funext s
    exact hm' s (m s) (by simp [sparseOfSeen, hseen s])
  rw [heq]
  exact hg

/-- Embed a proof about one full, original six-state machine into a complete
25-way coverage-search frontier. Its exact source instruction at each input
slot is the only branch recursively explored; the remaining 24 are open.
The list of slots must be duplicate-free and exhaust all unassigned cells. -/
noncomputable def singletonFrontier (good : Machine → Prop) (m : Machine)
    (hg : good m) (seen remaining : List Slot)
    (hnd : remaining.Nodup)
    (hdisj : ∀ s, s ∈ remaining → s ∉ seen)
    (hall : ∀ s : Slot, s ∈ seen ∨ s ∈ remaining) :
    FrontierAudit good (sparseOfSeen m seen) := by
  induction remaining generalizing seen with
  | nil =>
      apply FrontierAudit.certified
      apply singleCover good m seen
      · intro s
        rcases hall s with hs | hs
        · exact hs
        · simp at hs
      · exact hg
  | cons s rest ih =>
      have hnd2 : s ∉ rest ∧ rest.Nodup := List.nodup_cons.mp hnd
      have hs : s ∉ seen := hdisj s (by simp)
      apply FrontierAudit.branch (sparseOfSeen m seen) s
        (by simp [sparseOfSeen, hs])
      intro t ht
      by_cases ht0 : t = m s
      · subst t
        have hdisj2 : ∀ q, q ∈ rest → q ∉ s :: seen := by
          intro q hq hbad
          rcases List.mem_cons.mp hbad with hqs | hseen
          · subst q
            exact hnd2.1 hq
          · exact hdisj q (by simp [hq]) hseen
        have hall2 : ∀ q : Slot, q ∈ s :: seen ∨ q ∈ rest := by
          intro q
          rcases hall q with hseen | hrem
          · exact Or.inl (List.mem_cons_of_mem s hseen)
          · rcases List.mem_cons.mp hrem with hq | hq
            · exact Or.inl (List.mem_cons.mpr (Or.inl hq))
            · exact Or.inr hq
        have hc := ih (s :: seen) hnd2.2 hdisj2 hall2
        simpa only [sparseOfSeen_refine m seen s hs] using hc
      · exact FrontierAudit.unresolved _

/-- Starting from the globally unassigned six-state machine, the certified
path is precisely the chosen full machine and every alternative transition
is left explicit as an open disjoint cylinder. -/
noncomputable def singletonGlobal (good : Machine → Prop)
    (m : Machine) (hg : good m) :
    FrontierAudit good (fun _ => none) := by
  have hc := singletonFrontier good m hg [] auditSlots auditSlots_nodup
    (by simp) (fun s => Or.inr (auditSlots_complete s))
  have heq : sparseOfSeen m [] = (fun _ => none) := by
    funext s
    simp [sparseOfSeen]
  rw [← heq]
  exact hc

#print axioms singletonFrontier
#print axioms singletonGlobal
end BB6Coverage
