import QueueCoverageContract

namespace BB6.Agent5AdaptiveQueueCoverage

open BB6.Agent13QueueCoverage

/--
A finite source-queue checkpoint is sufficient for root coverage when both
residual lists are certified. Unlike `q0_rootGood_of_chunk_holdouts`, this
does not assume that the active queue has drained.
-/
theorem q0_rootGood_of_chunk_residuals
    {Node Machine : Type}
    (decide : Node → Decision Node)
    (Good : Machine → Prop)
    (Compatible : Node → Machine → Prop)
    (hsound : LocalClosure decide Good Compatible)
    (root : Node)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide root) ranges)
    (fuel : Nat)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).active ∨
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).holdout →
      ∀ m, Compatible y m → Good m) :
    ∀ m, Compatible root m → Good m := by
  intro m hm
  have hroot := q0_covers_root decide Good Compatible hsound root m hm
  rcases hroot with hgood | hrest
  · exact hgood
  · rcases hrest with hactive | hhold
    · rcases hactive with ⟨x, hx, hxm⟩
      obtain ⟨r, hr, hxr⟩ := hpart x hx
      have hchunk : coveredBy Good Compatible
          (chunkQueue (q0 decide root) r.1 r.2) m :=
        Or.inr (Or.inl ⟨x, hxr, hxm⟩)
      have hprocessed :=
        runUpdates_preserves_instance decide Good Compatible hsound fuel
          (chunkQueue (q0 decide root) r.1 r.2) m hchunk
      rcases hprocessed with hgood' | hrest'
      · exact hgood'
      · rcases hrest' with hactive' | hhold'
        · rcases hactive' with ⟨y, hy, hym⟩
          exact hcert r hr y (Or.inl hy) m hym
        · rcases hhold' with ⟨y, hy, hym⟩
          exact hcert r hr y (Or.inr hy) m hym
    · rcases hhold with ⟨x, hx, hxm⟩
      simp [q0] at hx

/--
List-valued adapter for checkpoint exporters that serialize active ++ held
as one residual roster.
-/
theorem q0_rootGood_of_chunk_residuals_append
    {Node Machine : Type}
    (decide : Node → Decision Node)
    (Good : Machine → Prop)
    (Compatible : Node → Machine → Prop)
    (hsound : LocalClosure decide Good Compatible)
    (root : Node)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide root) ranges)
    (fuel : Nat)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).active ++
          (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).holdout →
      ∀ m, Compatible y m → Good m) :
    ∀ m, Compatible root m → Good m := by
  apply q0_rootGood_of_chunk_residuals decide Good Compatible hsound root ranges hpart fuel
  intro r hr y hy m hym
  exact hcert r hr y (by simpa [List.mem_append] using hy) m hym

#print axioms q0_rootGood_of_chunk_residuals
#print axioms q0_rootGood_of_chunk_residuals_append

end BB6.Agent5AdaptiveQueueCoverage
