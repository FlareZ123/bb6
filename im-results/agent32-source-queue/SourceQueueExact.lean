import SourceQueueDrain
import WeightedFirstOneCover

namespace BB6.Agent32SourceExact
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5Enumerate62
open BB6.Agent13QueueCoverage BB6.Agent32SourceQueue BB6.Agent32SourceDrain

/-- Direct encoding of the three source classifier outcomes. In particular,
Halt retains its actual query slot, not just the fact of termination. -/
inductive SourceVerdict where
  | halt (slot : Slot)
  | nonhalt
  | unknown

def queueDecision (classify : SourceTM → SourceVerdict) (x : SourceNode) : QueueDecision SourceNode :=
  match classify x.tm with
  | .halt s => .halt (sourceExpand' x s)
  | .nonhalt => .nonhalt
  | .unknown => .unknown

/-- A source-semantics specification directly corresponding to Coq's
halts_at result (with the ordinary transition budget). A cross-language
semantic proof is needed to discharge it for the actual pinned decider. -/
def SourceClassifierSound (H : Nat) (classify : SourceTM → SourceVerdict) : Prop :=
  ∀ tm, match classify tm with
  | .halt s => ∃ n c, n ≤ H ∧ run tm n blank = some c ∧ readSlot c = s ∧ tm s = none
  | .nonhalt => NeverHalts tm
  | .unknown => True

theorem source_default_completion (tm : SourceTM) :
    weightedTNFDefaultCompletion (sourcePartial tm) = tm := by
  funext s
  cases h : tm s <;> simp [weightedTNFDefaultCompletion,sourcePartial,h]

theorem source_knownRun (tm : SourceTM) (n : Nat) :
    knownRun (sourcePartial tm) n = run tm n blank := by
  rw [weightedTNFKnownRun_eq_defaultRun,source_default_completion]

theorem source_evidence_of_classifier (H : Nat) (classify : SourceTM → SourceVerdict)
    (hs : SourceClassifierSound H classify) : SourceEvidence H (queueDecision classify) := by
  intro x _
  have h := hs x.tm
  cases hv : classify x.tm with
  | halt s =>
    simp only [hv] at h
    obtain ⟨n,c,hn,hr,hslot,hhole⟩ := h
    simp only [queueDecision,hv]
    refine ⟨n,c,?_,?_,hn,?_⟩
    · rwa [source_knownRun]
    · simp [sourcePartial,hslot,hhole]
    · rw [hslot]
  | nonhalt =>
    simp only [hv] at h
    simp only [queueDecision,hv]
    intro n
    rw [source_knownRun]
    have hn := h n
    cases hr : run x.tm n blank with
    | none => simp [hr] at hn
    | some c => exact ⟨c,rfl⟩
  | unknown => simp [queueDecision,hv]

theorem source_root_eq_firstOneCylinder :
    sourcePartial sourceRoot.tm = BB6.CoverageAdapter.firstOneCylinder := by
  funext s
  by_cases h : s = initialSlot <;>
    simp [sourceRoot,sourceRootTM,sourcePartial,BB6.CoverageAdapter.firstOneCylinder,refine,emptyTable,h]

/-- Final conditional global assembly. No queue-drain, fresh-label, root
normalization or individual short-halt premises remain exposed. -/
theorem exact_from_source_classifier (H B : Nat) (hB : H+6 ≤ B)
    (classify : SourceTM → SourceVerdict) (hs : SourceClassifierSound H classify)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 (queueDecision classify) sourceRoot) ranges)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates (queueDecision classify) BB6.Agent48Queue.maxT
        (chunkQueue (q0 (queueDecision classify) sourceRoot) r.1 r.2)).holdout → SourceSafe B y)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B := by
  have hc := source_queue_root_cover_maxT H B hB _ (source_evidence_of_classifier H classify hs) ranges hpart hcert
  rw [source_root_eq_firstOneCylinder] at hc
  exact exact_from_weighted_first_one B (by omega) hc champ

#print axioms source_default_completion
#print axioms source_knownRun
#print axioms source_evidence_of_classifier
#print axioms source_root_eq_firstOneCylinder
#print axioms exact_from_source_classifier
end BB6.Agent32SourceExact
