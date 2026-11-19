import SecondWordLeafGraft
import TranslatedFiveSlot

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage

/-!
Integrate Agent 27's five-slot, source-certified translated finite-support
cylinder into the existing depth-four physical frontier.

The four-slot parent is exactly the A/0, B/0, C/1, D/1 path already shown
open for every compatible completion by `secondWordParent_open_all`.
The generic `addCertificate_open_iff` theorem gives the exact partition:
the graft closes precisely the compatible five-slot cylinder and preserves
every other open completion of that parent.
-/

/-- Agent 27's four-slot parent is the same physical P4 cylinder used by
    the existing depth-four lasso audit. -/
theorem agent27P4_eq_secondWordP4 :
    agent27P4 = secondWordP4 := by
  rfl

/-- Every completion of Agent 27's P4 parent is an open leaf of the
    pre-existing depth-four physical frontier. -/
theorem agent27Parent_open_all (m : Machine)
    (hm : compatible agent27P4 m) :
    depth4ResidualAudit.open m := by
  apply secondWordParent_open_all m
  simpa [agent27P4_eq_secondWordP4] using hm

noncomputable def agent27GraftedAudit :
    FrontierAudit (DecidedBelow 6) emptyTable :=
  addCertificate depth4ResidualAudit agent27WordPump
    (agent27WordPump_cover 6)

/-- Exact open-set semantics of the integrated five-slot graft. -/
theorem agent27GraftedAudit_open_iff (m : Machine) :
    agent27GraftedAudit.open m ↔
      depth4ResidualAudit.open m ∧
        ¬ compatible agent27WordPump m := by
  simpa [agent27GraftedAudit] using
    (addCertificate_open_iff depth4ResidualAudit agent27WordPump
      (agent27WordPump_cover 6) m (empty_compatible m))

/-- On the P4 parent, the grafted open set is exactly the complement of
    Agent 27's five-slot cylinder. Thus no incompatible completion is
    silently discarded and no source-compatible completion remains open. -/
theorem agent27P4_exact_open_partition (m : Machine)
    (hm : compatible agent27P4 m) :
    agent27GraftedAudit.open m ↔
      ¬ compatible agent27WordPump m := by
  rw [agent27GraftedAudit_open_iff]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨agent27Parent_open_all m hm, h⟩

/-- Compatibility with the five-slot child implies compatibility with P4. -/
theorem agent27WordPump_parent_compatible (m : Machine)
    (hm : compatible agent27WordPump m) :
    compatible agent27P4 m := by
  have hchild : compatible
      (refine agent27P4 agent27E0 agent27E0Action) m := by
    rw [← agent27WordPump_is_P4_child]
    exact hm
  exact ((compatible_refine_iff agent27P4 m agent27E0 (by decide)
    agent27E0Action).mp hchild).1

/-- The new source cylinder was open in the old frontier and is closed by
    the integrated source certificate. -/
theorem agent27_leaf_closed (m : Machine)
    (hm : compatible agent27WordPump m) :
    depth4ResidualAudit.open m ∧
      ¬ agent27GraftedAudit.open m := by
  have hp := agent27WordPump_parent_compatible m hm
  refine ⟨agent27Parent_open_all m hp, ?_⟩
  intro hopen
  exact (agent27P4_exact_open_partition m hp).mp hopen hm

/-- The graft retains the global audit's exhaustive decided/open contract. -/
theorem agent27GraftedAudit_exhaustive (m : Machine) :
    DecidedBelow 6 m ∨ agent27GraftedAudit.open m :=
  agent27GraftedAudit.exhaustive m (empty_compatible m)

/-- The integrated audit still conserves the exact total mass of all raw
    six-state, two-symbol tables. -/
theorem agent27GraftedAudit_conserves :
    agent27GraftedAudit.report.1 + agent27GraftedAudit.report.2 = 25^12 := by
  calc
    _ = cylinderMass emptyTable := agent27GraftedAudit.report_conserves
    _ = 25^12 := by decide

#print axioms agent27P4_eq_secondWordP4
#print axioms agent27Parent_open_all
#print axioms agent27GraftedAudit_open_iff
#print axioms agent27P4_exact_open_partition
#print axioms agent27WordPump_parent_compatible
#print axioms agent27_leaf_closed
#print axioms agent27GraftedAudit_exhaustive
#print axioms agent27GraftedAudit_conserves

end BB6Coverage
