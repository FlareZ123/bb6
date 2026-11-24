import QueueImplication

namespace BB6.Agent8AdaptiveQueue
open BB6.Agent13QueueCoverage BB6.Agent32QueueImplication
universe u v

/-- A resumable, finite execution schedule. Split is a partition of the
actual active queue at that point, not an assumed partition of a historical
holdout roster. Advance consumes any chosen finite fuel. Stop keeps all
remaining obligations, including active nodes. -/
inductive Plan where
  | stop
  | advance (fuel : Nat) (next : Plan)
  | split (n : Nat) (left right : Plan)
  deriving Repr

/-- Preserve already-held nodes once at every split; neither subtree is
allowed to silently lose the held list. The two active sublists concatenate
exactly to the current active list, even for n=0 or n>length. -/
def obligations {Node : Type u} (decide : Node → QueueDecision Node) :
    Plan → CoverageQueue Node → List Node
  | .stop, q => q.active ++ q.holdout
  | .advance fuel next, q => obligations decide next (runUpdates decide fuel q)
  | .split n left right, q =>
      q.holdout ++ (obligations decide left ⟨q.active.take n, []⟩ ++
        obligations decide right ⟨q.active.drop n, []⟩)

/-- The source queue's already-proved update semantics are sufficient for
an arbitrary plan, without a global fixed fuel or a drain assumption. -/
theorem plan_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node) (Good : Machine → Prop)
    (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (plan : Plan) (q : CoverageQueue Node) (m : Machine)
    (h : coveredBy Good Compatible q m) :
    Good m ∨ ∃ x, x ∈ obligations decide plan q ∧ Compatible x m := by
  induction plan generalizing q with
  | stop =>
    rcases h with hg | ha | hh
    · exact Or.inl hg
    · obtain ⟨x,hx,hxm⟩ := ha
      exact Or.inr ⟨x, by simp [obligations,hx], hxm⟩
    · obtain ⟨x,hx,hxm⟩ := hh
      exact Or.inr ⟨x, by simp [obligations,hx], hxm⟩
  | advance fuel next ih =>
    exact ih _ (runUpdates_preserves_instance decide Good Compatible hsound fuel q m h)
  | split n left right ihl ihr =>
    rcases h with hg | ha | hh
    · exact Or.inl hg
    · obtain ⟨x,hx,hxm⟩ := ha
      have hmem : x ∈ q.active.take n ++ q.active.drop n := by
        rw [List.take_append_drop]; exact hx
      rcases List.mem_append.mp hmem with hl | hr
      · rcases ihl ⟨q.active.take n,[]⟩ (Or.inr (Or.inl ⟨x,hl,hxm⟩)) with hg | ⟨y,hy,hym⟩
        · exact Or.inl hg
        · exact Or.inr ⟨y, by simp [obligations,hy], hym⟩
      · rcases ihr ⟨q.active.drop n,[]⟩ (Or.inr (Or.inl ⟨x,hr,hxm⟩)) with hg | ⟨y,hy,hym⟩
        · exact Or.inl hg
        · exact Or.inr ⟨y, by simp [obligations,hy], hym⟩
    · obtain ⟨x,hx,hxm⟩ := hh
      exact Or.inr ⟨x, by simp [obligations,hx], hxm⟩

/-- Backwards form used by the weighted TNF source bridge. A plan may stop
while active nodes remain: those active nodes are then part of its exact
certificate obligations. -/
theorem plan_safe {Node : Type u}
    (decide : Node → QueueDecision Node) (Safe : Node → Prop)
    (hsound : LocalClosure decide Safe) (plan : Plan) (q : CoverageQueue Node)
    (hcert : ∀ y, y ∈ obligations decide plan q → Safe y) :
    (∀ x, x ∈ q.active → Safe x) ∧ (∀ x, x ∈ q.holdout → Safe x) := by
  classical
  have hh := localClosure_classifier decide Safe hsound
  constructor
  · intro x hx
    apply Classical.byContradiction; intro hb
    rcases plan_preserves_instance decide (fun _ : Unit => False)
      (fun x _ => ¬ Safe x) hh plan q () (Or.inr (Or.inl ⟨x,hx,hb⟩)) with hg | ⟨y,hy,hybad⟩
    · exact hg
    · exact hybad (hcert y hy)
  · intro x hx
    apply Classical.byContradiction; intro hb
    rcases plan_preserves_instance decide (fun _ : Unit => False)
      (fun x _ => ¬ Safe x) hh plan q () (Or.inr (Or.inr ⟨x,hx,hb⟩)) with hg | ⟨y,hy,hybad⟩
    · exact hg
    · exact hybad (hcert y hy)

/-- Exact coverage of the four-BFS root with arbitrary finite schedules.
There is no additional range-membership or same-output-order hypothesis. -/
theorem q0_safe_of_plan {Node : Type u}
    (decide : Node → QueueDecision Node) (Safe : Node → Prop)
    (hsound : LocalClosure decide Safe) (root : Node) (plan : Plan)
    (hcert : ∀ y, y ∈ obligations decide plan (q0 decide root) → Safe y) :
    Safe root := by
  classical
  apply Classical.byContradiction; intro hb
  have hh := localClosure_classifier decide Safe hsound
  have hroot := q0_covers_root decide (fun _ : Unit => False)
    (fun x _ => ¬ Safe x) hh root () hb
  rcases plan_preserves_instance decide (fun _ : Unit => False)
    (fun x _ => ¬ Safe x) hh plan (q0 decide root) () hroot with hg | ⟨y,hy,hybad⟩
  · exact hg
  · exact hybad (hcert y hy)

/-- Directly assemble a source checkpoint certificate from independent
proofs of the held nodes and the two active ranges. Useful when branches
have been evaluated on separate workers. -/
theorem split_obligations_safe {Node : Type u}
    (decide : Node → QueueDecision Node) (Safe : Node → Prop)
    (q : CoverageQueue Node) (n : Nat) (left right : Plan)
    (hheld : ∀ x, x ∈ q.holdout → Safe x)
    (hleft : ∀ x, x ∈ obligations decide left ⟨q.active.take n, []⟩ → Safe x)
    (hright : ∀ x, x ∈ obligations decide right ⟨q.active.drop n, []⟩ → Safe x) :
    ∀ x, x ∈ obligations decide (.split n left right) q → Safe x := by
  intro x hx
  simp only [obligations, List.mem_append] at hx
  rcases hx with h | h | h
  · exact hheld x h
  · exact hleft x h
  · exact hright x h

#print axioms plan_preserves_instance
#print axioms plan_safe
#print axioms q0_safe_of_plan
#print axioms split_obligations_safe
end BB6.Agent8AdaptiveQueue
