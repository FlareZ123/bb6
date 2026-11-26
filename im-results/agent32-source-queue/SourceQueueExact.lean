import SourceQueueDrain
import WeightedFirstOneCover
import SourceFiniteSemantics

namespace BB6.Agent32SourceExact
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5Enumerate62
open BB6.Agent13QueueCoverage BB6.Agent32SourceQueue BB6.Agent32SourceDrain
open BB6.Agent32FiniteSource

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
    exact Option.isSome_iff_exists.mp (h n)
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


/-- Exactness from a finite source checkpoint, certifying both active and
held residuals. Unlike the drain-based interface, this theorem accepts any
finite fuel and leaves the exact residual partition explicit. -/
theorem exact_from_source_classifier_residuals (H B : Nat) (hB : H+6 ≤ B)
    (classify : SourceTM → SourceVerdict) (hs : SourceClassifierSound H classify)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 (queueDecision classify) sourceRoot) ranges)
    (fuel : Nat)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates (queueDecision classify) fuel
        (chunkQueue (q0 (queueDecision classify) sourceRoot) r.1 r.2)).active ∨
      y ∈ (runUpdates (queueDecision classify) fuel
        (chunkQueue (q0 (queueDecision classify) sourceRoot) r.1 r.2)).holdout →
      SourceSafe B y)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  have hc := source_queue_root_cover_residuals H B hB _
    (source_evidence_of_classifier H classify hs) ranges hpart fuel hcert
  rw [source_root_eq_firstOneCylinder] at hc
  exact exact_from_weighted_first_one B (by omega) hc champ



/-- Exactness from an arbitrary finite adaptive source-queue plan. Unlike
fixed-fuel chunk adapters, this accepts nonuniform advances and recursive
active-list splits while preserving every stopped active and held residual. -/
theorem exact_from_source_classifier_plan (H B : Nat) (hB : H+6 ≤ B)
    (classify : SourceTM → SourceVerdict) (hs : SourceClassifierSound H classify)
    (plan : BB6.Agent8AdaptiveQueue.Plan)
    (hcert : ∀ y, y ∈ BB6.Agent8AdaptiveQueue.obligations (queueDecision classify) plan
      (q0 (queueDecision classify) sourceRoot) → SourceSafe B y)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  have hc := source_queue_root_cover_plan H B hB _
    (source_evidence_of_classifier H classify hs) plan hcert
  rw [source_root_eq_firstOneCylinder] at hc
  exact exact_from_weighted_first_one B (by omega) hc champ


#print axioms source_default_completion
#print axioms source_knownRun
#print axioms source_evidence_of_classifier
#print axioms source_root_eq_firstOneCylinder
#print axioms exact_from_source_classifier

/-- The finite-list hypothesis is the exact shape of the upstream Coq
certificate after replacing the stream tape with its finite representation. -/
def FiniteClassifierSound (H : Nat) (classify : SourceTM → SourceVerdict) : Prop :=
  ∀ tm, match classify tm with
  | .halt s => ∃ n c, n ≤ H ∧ finiteRun tm n finiteBlank = some c ∧ query c = s ∧ tm s = none
  | .nonhalt => ∀ n, ∃ c, finiteRun tm n finiteBlank = some c
  | .unknown => True

theorem source_classifier_sound_of_finite (H : Nat) (classify : SourceTM → SourceVerdict)
    (hs : FiniteClassifierSound H classify) : SourceClassifierSound H classify := by
  intro tm
  have h := hs tm
  cases hv : classify tm with
  | halt s =>
    simp only [hv] at h ⊢
    obtain ⟨n,c,hn,hr,hq,hh⟩ := h
    obtain ⟨d,hd,hdq,hdh⟩ := finite_halt_sound tm n c s hr hq hh
    exact ⟨n,d,hn,hd,hdq,hdh⟩
  | nonhalt =>
    simp only [hv] at h ⊢
    exact (finite_never_iff tm).mp h
  | unknown => trivial

theorem exact_from_finite_classifier (H B : Nat) (hB : H+6 ≤ B)
    (classify : SourceTM → SourceVerdict) (hs : FiniteClassifierSound H classify)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 (queueDecision classify) sourceRoot) ranges)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates (queueDecision classify) BB6.Agent48Queue.maxT
        (chunkQueue (q0 (queueDecision classify) sourceRoot) r.1 r.2)).holdout → SourceSafe B y)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) : BB6.Coverage.ExactBB6 B :=
  exact_from_source_classifier H B hB classify (source_classifier_sound_of_finite H classify hs)
    ranges hpart hcert champ


/-- Same finite-checkpoint interface, stated directly for the upstream
finite-list classifier specification. -/
theorem exact_from_finite_classifier_residuals (H B : Nat) (hB : H+6 ≤ B)
    (classify : SourceTM → SourceVerdict) (hs : FiniteClassifierSound H classify)
    (ranges : List (Nat × Nat))
    (hpart : ChunkPartition (q0 (queueDecision classify) sourceRoot) ranges)
    (fuel : Nat)
    (hcert : ∀ r, r ∈ ranges → ∀ y,
      y ∈ (runUpdates (queueDecision classify) fuel
        (chunkQueue (q0 (queueDecision classify) sourceRoot) r.1 r.2)).active ∨
      y ∈ (runUpdates (queueDecision classify) fuel
        (chunkQueue (q0 (queueDecision classify) sourceRoot) r.1 r.2)).holdout →
      SourceSafe B y)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_source_classifier_residuals H B hB classify
    (source_classifier_sound_of_finite H classify hs)
    ranges hpart fuel hcert champ



/-- Finite-list classifier specialization of the arbitrary adaptive-plan
exactness theorem. -/
theorem exact_from_finite_classifier_plan (H B : Nat) (hB : H+6 ≤ B)
    (classify : SourceTM → SourceVerdict) (hs : FiniteClassifierSound H classify)
    (plan : BB6.Agent8AdaptiveQueue.Plan)
    (hcert : ∀ y, y ∈ BB6.Agent8AdaptiveQueue.obligations (queueDecision classify) plan
      (q0 (queueDecision classify) sourceRoot) → SourceSafe B y)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_source_classifier_plan H B hB classify
    (source_classifier_sound_of_finite H classify hs) plan hcert champ


#print axioms source_classifier_sound_of_finite
#print axioms exact_from_finite_classifier
#print axioms exact_from_source_classifier_residuals
#print axioms exact_from_finite_classifier_residuals
#print axioms exact_from_source_classifier_plan
#print axioms exact_from_finite_classifier_plan
end BB6.Agent32SourceExact
