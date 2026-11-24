import Lean

namespace BB6.Agent13QueueCoverage

universe u v

/-- A generic two-list work queue. The node type may retain the full partial
    machine; unlike the potential projection, this contract does not erase it. -/
structure CoverageQueue (Node : Type u) where
  active : List Node
  holdout : List Node

/-- A source decision either certifies the current cylinder, expands it into
    non-halt children, or leaves it unresolved. -/
inductive QueueDecision (Node : Type u) where
  | halt (children : List Node)
  | nonhalt
  | unknown

def update {Node : Type u} (decide : Node → QueueDecision Node)
    (q : CoverageQueue Node) : CoverageQueue Node :=
  match q.active with
  | [] => q
  | x :: xs =>
      match decide x with
      | .halt children => ⟨children ++ xs, q.holdout⟩
      | .nonhalt => ⟨xs, q.holdout⟩
      | .unknown => ⟨xs, x :: q.holdout⟩

def bfsHoldAfter {Node : Type u} (decide : Node → QueueDecision Node)
    (x : Node) (hold : List Node) : List Node :=
  match decide x with
  | .halt children => children ++ hold
  | .nonhalt => hold
  | .unknown => x :: hold

/-- Process each node that was active at the beginning of this pass exactly
    once. Newly expanded or unknown nodes wait in the holdout list. -/
def bfsAux {Node : Type u} (decide : Node → QueueDecision Node) :
    List Node → List Node → List Node
  | [], hold => hold
  | x :: xs, hold => bfsAux decide xs (bfsHoldAfter decide x hold)

def bfsRound {Node : Type u} (decide : Node → QueueDecision Node)
    (q : CoverageQueue Node) : CoverageQueue Node :=
  ⟨bfsAux decide q.active q.holdout, []⟩

def fourBfsPasses {Node : Type u} (decide : Node → QueueDecision Node)
    (q : CoverageQueue Node) : CoverageQueue Node :=
  bfsRound decide (bfsRound decide (bfsRound decide (bfsRound decide q)))

/-- Fixed-fuel serial queue processing, with early termination when active
    is empty. -/
def runUpdates {Node : Type u} (decide : Node → QueueDecision Node) :
    Nat → CoverageQueue Node → CoverageQueue Node
  | 0, q => q
  | fuel + 1, q =>
      match q.active with
      | [] => q
      | _ :: _ => runUpdates decide fuel (update decide q)

/-- A concrete completion is either already certified, represented by an
    active node, or represented by a held-out node. -/
def coveredBy {Node : Type u} {Machine : Type v}
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (q : CoverageQueue Node) (m : Machine) : Prop :=
  Good m ∨
    (∃ x, x ∈ q.active ∧ Compatible x m) ∨
    (∃ x, x ∈ q.holdout ∧ Compatible x m)

def QueueCovers {Node : Type u} {Machine : Type v}
    (root : Node) (Good : Machine → Prop)
    (Compatible : Node → Machine → Prop) (q : CoverageQueue Node) : Prop :=
  ∀ m, Compatible root m → coveredBy Good Compatible q m

/-- The only local mathematical obligation on the source decider:
    Halt certifies the halt-transition part and expands all remaining
    non-halt completions; Nonhalt certifies the whole cylinder. -/
def ClassifierSound {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop) : Prop :=
  ∀ x m, Compatible x m →
    match decide x with
    | .halt children =>
        Good m ∨ (∃ y, y ∈ children ∧ Compatible y m)
    | .nonhalt => Good m
    | .unknown => True

theorem update_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (q : CoverageQueue Node) (m : Machine)
    (hcover : coveredBy Good Compatible q m) :
    coveredBy Good Compatible (update decide q) m := by
  cases q with
  | mk active hold =>
      cases active with
      | nil =>
          simpa [update, coveredBy] using hcover
      | cons x xs =>
          rcases hcover with hgood | hrest
          · exact Or.inl hgood
          · rcases hrest with hactive | hhold
            · rcases hactive with ⟨y, hy, hym⟩
              simp only [List.mem_cons] at hy
              rcases hy with hEq | hyTail
              · subst y
                cases hd : decide x with
                | halt children =>
                    have hs := hsound x m hym
                    simp [hd] at hs
                    rcases hs with hg | ⟨z, hz, hzm⟩
                    · exact Or.inl hg
                    · exact Or.inr (Or.inl ⟨z, by simp [update, hd, hz], hzm⟩)
                | nonhalt =>
                    have hs := hsound x m hym
                    simp [hd] at hs
                    exact Or.inl hs
                | unknown =>
                    exact Or.inr (Or.inr ⟨x, by simp [update, hd], hym⟩)
              · cases hd : decide x with
                | halt children =>
                    exact Or.inr (Or.inl ⟨y, by simp [update, hd, hyTail], hym⟩)
                | nonhalt =>
                    exact Or.inr (Or.inl ⟨y, by simp [update, hd, hyTail], hym⟩)
                | unknown =>
                    exact Or.inr (Or.inl ⟨y, by simp [update, hd, hyTail], hym⟩)
            · rcases hhold with ⟨y, hy, hym⟩
              cases hd : decide x with
              | halt children =>
                  exact Or.inr (Or.inr ⟨y, by simp [update, hd, hy], hym⟩)
              | nonhalt =>
                  exact Or.inr (Or.inr ⟨y, by simp [update, hd, hy], hym⟩)
              | unknown =>
                  exact Or.inr (Or.inr ⟨y, by simp [update, hd, hy], hym⟩)

theorem bfsStep_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (x : Node) (xs hold : List Node) (m : Machine)
    (hcover : coveredBy Good Compatible ⟨x :: xs, hold⟩ m) :
    coveredBy Good Compatible ⟨xs, bfsHoldAfter decide x hold⟩ m := by
  rcases hcover with hgood | hrest
  · exact Or.inl hgood
  · rcases hrest with hactive | hhold
    · rcases hactive with ⟨y, hy, hym⟩
      simp only [List.mem_cons] at hy
      rcases hy with hEq | hyTail
      · subst y
        cases hd : decide x with
        | halt children =>
            have hs := hsound x m hym
            simp [hd] at hs
            rcases hs with hg | ⟨z, hz, hzm⟩
            · exact Or.inl hg
            · exact Or.inr (Or.inr ⟨z, by simp [bfsHoldAfter, hd, hz], hzm⟩)
        | nonhalt =>
            have hs := hsound x m hym
            simp [hd] at hs
            exact Or.inl hs
        | unknown =>
            exact Or.inr (Or.inr ⟨x, by simp [bfsHoldAfter, hd], hym⟩)
      · exact Or.inr (Or.inl ⟨y, hyTail, hym⟩)
    · rcases hhold with ⟨y, hy, hym⟩
      cases hd : decide x with
      | halt children =>
          exact Or.inr (Or.inr ⟨y, by simp [bfsHoldAfter, hd, hy], hym⟩)
      | nonhalt =>
          exact Or.inr (Or.inr ⟨y, by simp [bfsHoldAfter, hd, hy], hym⟩)
      | unknown =>
          exact Or.inr (Or.inr ⟨y, by simp [bfsHoldAfter, hd, hy], hym⟩)

theorem bfsAux_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible) :
    ∀ xs hold m, coveredBy Good Compatible ⟨xs, hold⟩ m →
      coveredBy Good Compatible ⟨bfsAux decide xs hold, []⟩ m := by
  intro xs
  induction xs with
  | nil =>
      intro hold m hcover
      simpa [bfsAux, coveredBy] using hcover
  | cons x xs ih =>
      intro hold m hcover
      have hstep := bfsStep_preserves_instance decide Good Compatible hsound
        x xs hold m hcover
      have hrec := ih (bfsHoldAfter decide x hold) m hstep
      simpa [bfsAux] using hrec

theorem bfsRound_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (q : CoverageQueue Node) (m : Machine)
    (hcover : coveredBy Good Compatible q m) :
    coveredBy Good Compatible (bfsRound decide q) m := by
  cases q with
  | mk active hold =>
      exact bfsAux_preserves_instance decide Good Compatible hsound active hold m hcover

theorem fourBfsPasses_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (q : CoverageQueue Node) (m : Machine)
    (hcover : coveredBy Good Compatible q m) :
    coveredBy Good Compatible (fourBfsPasses decide q) m := by
  have h1 := bfsRound_preserves_instance decide Good Compatible hsound q m hcover
  have h2 := bfsRound_preserves_instance decide Good Compatible hsound
    (bfsRound decide q) m h1
  have h3 := bfsRound_preserves_instance decide Good Compatible hsound
    (bfsRound decide (bfsRound decide q)) m h2
  have h4 := bfsRound_preserves_instance decide Good Compatible hsound
    (bfsRound decide (bfsRound decide (bfsRound decide q))) m h3
  simpa [fourBfsPasses] using h4

def rootQueue {Node : Type u} (root : Node) : CoverageQueue Node :=
  ⟨[root], []⟩

def q0 {Node : Type u} (decide : Node → QueueDecision Node) (root : Node) :
    CoverageQueue Node :=
  fourBfsPasses decide (rootQueue root)

theorem rootQueue_covered {Node : Type u} {Machine : Type v}
    (root : Node) (Good : Machine → Prop)
    (Compatible : Node → Machine → Prop) (m : Machine)
    (hm : Compatible root m) :
    coveredBy Good Compatible (rootQueue root) m :=
  Or.inr (Or.inl ⟨root, by simp [rootQueue], hm⟩)

theorem q0_covers_root {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible) (root : Node) :
    QueueCovers root Good Compatible (q0 decide root) := by
  intro m hm
  exact fourBfsPasses_preserves_instance decide Good Compatible hsound
    (rootQueue root) m (rootQueue_covered root Good Compatible m hm)

theorem q0_holdout_empty {Node : Type u}
    (decide : Node → QueueDecision Node) (root : Node) :
    (q0 decide root).holdout = [] := by
  simp [q0, fourBfsPasses, bfsRound]

def chunkQueue {Node : Type u} (q : CoverageQueue Node) (l sz : Nat) :
    CoverageQueue Node :=
  ⟨(q.active.drop l).take sz, q.holdout⟩

def ChunkPartition {Node : Type u} (q : CoverageQueue Node)
    (ranges : List (Nat × Nat)) : Prop :=
  ∀ x, x ∈ q.active →
    ∃ r, r ∈ ranges ∧ x ∈ (chunkQueue q r.1 r.2).active

theorem runUpdates_preserves_instance {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible) :
    ∀ fuel q m, coveredBy Good Compatible q m →
      coveredBy Good Compatible (runUpdates decide fuel q) m := by
  intro fuel
  induction fuel with
  | zero =>
      intro q m hcover
      simpa [runUpdates] using hcover
  | succ fuel ih =>
      intro q m hcover
      cases hq : q.active with
      | nil =>
          simpa [runUpdates, hq] using hcover
      | cons x xs =>
          have hstep := update_preserves_instance decide Good Compatible hsound q m hcover
          have hrec := ih (update decide q) m hstep
          simpa [runUpdates, hq] using hrec

/-- If the source chunk ranges cover every active q0 node, then after each
    chunk has drained, every root completion is either already Good or is
    compatible with a node in one of the final holdout outputs. -/
theorem chunkOutputs_cover_root {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (root : Node) (q : CoverageQueue Node)
    (hroot : QueueCovers root Good Compatible q)
    (hqhold : q.holdout = [])
    (ranges : List (Nat × Nat)) (hpart : ChunkPartition q ranges)
    (fuel : Nat)
    (hdrain : ∀ r, r ∈ ranges →
      (runUpdates decide fuel (chunkQueue q r.1 r.2)).active = []) :
    ∀ m, Compatible root m →
      Good m ∨
        (∃ r, r ∈ ranges ∧ ∃ y,
          y ∈ (runUpdates decide fuel (chunkQueue q r.1 r.2)).holdout ∧
          Compatible y m) := by
  intro m hm
  have h := hroot m hm
  rcases h with hgood | hrest
  · exact Or.inl hgood
  · rcases hrest with hactive | hhold
    · rcases hactive with ⟨x, hx, hxm⟩
      obtain ⟨r, hr, hxr⟩ := hpart x hx
      have hchunk : coveredBy Good Compatible (chunkQueue q r.1 r.2) m := by
        simp [coveredBy, chunkQueue, hqhold]
        exact Or.inr (Or.inl ⟨x, hxr, hxm⟩)
      have hprocessed := runUpdates_preserves_instance decide Good Compatible hsound
        fuel (chunkQueue q r.1 r.2) m hchunk
      have hdr := hdrain r hr
      rcases hprocessed with hg | hprocessed
      · exact Or.inl hg
      · rcases hprocessed with hactive' | hhold'
        · rcases hactive' with ⟨y, hy, hym⟩
          have hfalse : False := by simpa [hdr] using hy
          exact False.elim hfalse
        · rcases hhold' with ⟨y, hy, hym⟩
          exact Or.inr ⟨r, hr, y, hy, hym⟩
    · rcases hhold with ⟨x, hx, hxm⟩
      simp [hqhold] at hx

/-- The final source-to-BB6 closure contract. Once the q0 chunk partition is
    exhaustive, every chunk drains, and every final holdout node is certified
    for all of its compatible completions, the whole root cylinder is Good. -/
theorem rootGood_of_chunk_holdouts {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (root : Node) (q : CoverageQueue Node)
    (hroot : QueueCovers root Good Compatible q)
    (hqhold : q.holdout = [])
    (ranges : List (Nat × Nat)) (hpart : ChunkPartition q ranges)
    (fuel : Nat)
    (hdrain : ∀ r, r ∈ ranges →
      (runUpdates decide fuel (chunkQueue q r.1 r.2)).active = [])
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue q r.1 r.2)).holdout →
        ∀ m, Compatible y m → Good m) :
    ∀ m, Compatible root m → Good m := by
  intro m hm
  rcases chunkOutputs_cover_root decide Good Compatible hsound root q
      hroot hqhold ranges hpart fuel hdrain m hm with hg | hleft
  · exact hg
  · rcases hleft with ⟨r, hr, y, hy, hym⟩
    exact hcert r hr y hy m hym

/-- Specialization to the four-pass q0 rooted at the supplied partial node. -/
theorem q0_rootGood_of_chunk_holdouts {Node : Type u} {Machine : Type v}
    (decide : Node → QueueDecision Node)
    (Good : Machine → Prop) (Compatible : Node → Machine → Prop)
    (hsound : ClassifierSound decide Good Compatible)
    (root : Node) (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide root) ranges)
    (fuel : Nat)
    (hdrain : ∀ r, r ∈ ranges →
      (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).active = [])
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).holdout →
        ∀ m, Compatible y m → Good m) :
    ∀ m, Compatible root m → Good m := by
  apply rootGood_of_chunk_holdouts decide Good Compatible hsound root
    (q0 decide root) (q0_covers_root decide Good Compatible hsound root)
    (q0_holdout_empty decide root) ranges hpart fuel hdrain hcert

#print axioms update_preserves_instance
#print axioms bfsAux_preserves_instance
#print axioms fourBfsPasses_preserves_instance
#print axioms q0_covers_root
#print axioms runUpdates_preserves_instance
#print axioms chunkOutputs_cover_root
#print axioms rootGood_of_chunk_holdouts
#print axioms q0_rootGood_of_chunk_holdouts

end BB6.Agent13QueueCoverage
