import Enumerate62Adapter
import QueueImplication
import AdaptiveQueuePlan
import AdaptiveQueueCoverage

namespace BB6.Agent32SourceQueue
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5Enumerate62
open BB6.Agent13QueueCoverage BB6.Agent32QueueImplication
open BB6.Agent5AdaptiveQueueCoverage BB6.Agent8AdaptiveQueue

theorem reachable_cut_positive {x : SourceNode} (h : SourceReachable x) : 0 < x.fresh := by
  induction h with
  | root => decide
  | @child x slot mv hp hh hs hd ih =>
    exact Nat.lt_of_lt_of_le ih (sourceChildFresh_ge x mv)

theorem reachable_firstOne {x : SourceNode} (h : SourceReachable x) :
    sourcePartial x.tm initialSlot = some (some ⟨true,true,1⟩) := by
  induction h with
  | root => exact sourceRoot_action
  | @child x slot mv hp hh hs hd ih =>
    rw [sourceChild_partial]
    exact refine_preserves_firstOne _ _ _ (by simp [sourcePartial, hh]) ih

theorem halt_budget_weight (H B n : Nat) (p : PartialMachine)
    (hH : H+6 ≤ B) (hn : n ≤ H) :
    ∀ d ∈ possibleDelays p 0, d+n+1 ≤ B := by
  intro d hd
  have hlt : d < 6 := List.mem_range.mp (List.mem_filter.mp hd).1
  omega

def SourceSafe (B : Nat) (x : SourceNode) : Prop :=
  SourceReachable x → ∀ m, compatible (sourcePartial x.tm) m → WeightedBound B m

def SourceEvidence (H : Nat) (decide : SourceNode → QueueDecision SourceNode) : Prop :=
  ∀ x, SourceReachable x →
    match decide x with
    | .halt children => ∃ n c,
        knownRun (sourcePartial x.tm) n = some c ∧
        sourcePartial x.tm (readSlot c) = none ∧ n ≤ H ∧
        children = sourceExpand' x (readSlot c)
    | .nonhalt => weightedTNFKnownRunForever (sourcePartial x.tm)
    | .unknown => True

theorem source_localClosure (H B : Nat) (hB : H+6 ≤ B)
    (decide : SourceNode → QueueDecision SourceNode)
    (hevidence : SourceEvidence H decide) : LocalClosure decide (SourceSafe B) := by
  intro x
  cases hd : decide x with
  | unknown => trivial
  | nonhalt =>
    intro hx m hm
    have he := hevidence x hx
    rw [hd] at he
    exact weighted_never B m (weightedTNFKnownRunForever_sound _ he m hm)
  | halt children =>
    intro hall hx
    have he := hevidence x hx
    rw [hd] at he
    obtain ⟨n,c,hrun,hhole,hn,hchildren⟩ := he
    have hcut := reachable_cut_positive hx
    have hf := reachable_firstOne hx
    have hweight := halt_budget_weight H B n
      (refine (sourcePartial x.tm) (readSlot c) none) hB hn
    by_cases hlast : x.holes.length = 1
    · exact (source_last_hole_cover B x n c hx hlast hf hrun hhole hweight).sound
    · have hsupport := sourceSupport_to_tnfSupport x.tm x.fresh (sourceReachable_wf hx).2.2.2
      have hslot : (readSlot c).1.val < x.fresh :=
        knownRun_support _ _ hcut hsupport n c hrun
      have htmhole : x.tm (readSlot c) = none := by
        cases ht : x.tm (readSlot c) with
        | none => rfl
        | some mv => simp [sourcePartial, ht] at hhole
      have hchild (mv : Move) (hmv : mv.next.val ≤ x.fresh) :
          ∀ m, compatible (sourcePartial (sourceChild x (readSlot c) mv).tm) m → WeightedBound B m := by
        have hmem : sourceChild x (readSlot c) mv ∈ children := by
          rw [hchildren, sourceExpand', ite_eq_right hlast]
          exact (sourceExpand_child_iff _ _ _).mpr ⟨mv,hmv,rfl⟩
        exact hall _ hmem (SourceReachable.child hx htmhole hslot hmv)
      exact (source_expand_cover B x n c hx hcut hf hrun hhole hweight
        (fun mv hlt => hchild mv (Nat.le_of_lt hlt))
        (fun q hq w r => hchild ⟨w,r,q⟩ (by change q.val ≤ x.fresh; omega))).sound


/-- Root safety from finite source checkpoints when both active and held
residual nodes are certified. This removes the queue-drain premise. -/
theorem q0_safe_of_chunk_residuals
    (decide : SourceNode → QueueDecision SourceNode)
    (Safe : SourceNode → Prop)
    (hsound : LocalClosure decide Safe)
    (root : SourceNode)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide root) ranges)
    (fuel : Nat)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).active ∨
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide root) r.1 r.2)).holdout →
      Safe y) : Safe root := by
  classical
  apply Classical.byContradiction
  intro hb
  exact q0_rootGood_of_chunk_residuals decide (fun _ : Unit => False)
    (fun x _ => ¬ Safe x)
    (localClosure_classifier decide Safe hsound)
    root ranges hpart fuel
    (fun r hr y hy _ hbad => hbad (hcert r hr y hy)) () hb

/-- Source-specific weighted Cover interface for finite checkpoints. Every
active or held residual must carry a score-B certificate; no drain is needed. -/
theorem source_queue_root_cover_residuals (H B : Nat) (hB : H+6 ≤ B)
    (decide : SourceNode → QueueDecision SourceNode)
    (hevidence : SourceEvidence H decide)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide sourceRoot) ranges)
    (fuel : Nat)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide sourceRoot) r.1 r.2)).active ∨
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide sourceRoot) r.1 r.2)).holdout →
      SourceSafe B y) :
    Cover (WeightedBound B) (sourcePartial sourceRoot.tm) := by
  have hs := q0_safe_of_chunk_residuals decide (SourceSafe B)
    (source_localClosure H B hB decide hevidence) sourceRoot ranges hpart fuel hcert
  exact .leaf _ (hs SourceReachable.root)



/-- Fully adaptive source-queue interface. The plan may use different
finite fuels and active-list splits at every node; every stopped active or
held residual remains an explicit certificate obligation. -/
theorem source_queue_root_cover_plan (H B : Nat) (hB : H+6 ≤ B)
    (decide : SourceNode → QueueDecision SourceNode)
    (hevidence : SourceEvidence H decide)
    (plan : Plan)
    (hcert : ∀ y, y ∈ obligations decide plan (q0 decide sourceRoot) →
      SourceSafe B y) :
    Cover (WeightedBound B) (sourcePartial sourceRoot.tm) := by
  have hs := q0_safe_of_plan decide (SourceSafe B)
    (source_localClosure H B hB decide hevidence) sourceRoot plan hcert
  exact .leaf _ (hs SourceReachable.root)


theorem source_queue_root_cover (H B : Nat) (hB : H+6 ≤ B)
    (decide : SourceNode → QueueDecision SourceNode)
    (hevidence : SourceEvidence H decide)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 decide sourceRoot) ranges) (fuel : Nat)
    (hdrain : ∀ r, r ∈ ranges →
      (runUpdates decide fuel (chunkQueue (q0 decide sourceRoot) r.1 r.2)).active = [])
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates decide fuel (chunkQueue (q0 decide sourceRoot) r.1 r.2)).holdout → SourceSafe B y) :
    Cover (WeightedBound B) (sourcePartial sourceRoot.tm) := by
  have hs := q0_safe_of_chunk_holdouts decide (SourceSafe B)
    (source_localClosure H B hB decide hevidence) sourceRoot ranges hpart fuel hdrain hcert
  exact .leaf _ (hs SourceReachable.root)

#print axioms reachable_cut_positive
#print axioms reachable_firstOne
#print axioms halt_budget_weight
#print axioms source_localClosure
#print axioms source_queue_root_cover
#print axioms source_queue_root_cover_plan
#print axioms q0_safe_of_chunk_residuals
#print axioms source_queue_root_cover_residuals
end BB6.Agent32SourceQueue
