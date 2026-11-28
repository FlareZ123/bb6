import PartialWeightExact
import AuditScore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
An arithmetic least-bound evaluator for the partial-Audit coverage trees used
in the six-state Busy Beaver search. Under explicitly bounded residuals, the
folded score is an exact universal weighted bound, not merely a sufficient
one. If all residuals are unconditionally nonhalting, a positive folded score
is realized by a compatible halting completion.
-/

namespace BB6.Agent11PartialWeightScore

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47PartialAudit BB6.Agent32AuditReweight
open BB6.Agent10ExactAuditWeight BB6.Agent11PartialWeightExact

/-- The cheap quick weight check agrees exactly with the original expensive
    possible-blank-delay weight check. -/
theorem quick_weight_iff (B : Nat) (p : PartialMachine)
    (n : Nat) (s : Slot) :
    (quickWeight B p n s = true) ↔ weightOK p s n B = true := by
  constructor
  · exact quickWeight_sound
  · intro hw
    by_cases hsmall : n + 6 ≤ B
    · simp [quickWeight, hsmall]
    · simpa [quickWeight, hsmall] using hw

theorem audit_score_le_weightAudit (p : PartialMachine)
    (t : Audit) (B : Nat) :
    auditScore p t ≤ B ↔ weightAudit B p t = true := by
  induction t generalizing p with
  | last n s =>
    exact (queryScore_le p n s B).trans (quick_weight_iff B p n s).symm
  | cycle e k r b => simp [auditScore, weightAudit]
  | far rev d C => simp [auditScore, weightAudit]
  | proven q safe => simp [auditScore, weightAudit]
  | split n s kids ih =>
    simp only [auditScore, weightAudit, Nat.max_le, Bool.and_eq_true, maxList_le]
    constructor
    · rintro ⟨hq,hk⟩
      refine ⟨(quick_weight_iff B p n s).mpr ((queryScore_le p n s B).mp hq),
        allMoves_of _ ?_⟩
      intro mv
      exact (ih mv _).mp (hk _ (List.mem_map.mpr ⟨mv,mem_moves mv,rfl⟩))
    · rintro ⟨hq,hk⟩
      refine ⟨(queryScore_le p n s B).mpr ((quick_weight_iff B p n s).mp hq), ?_⟩
      intro x hx
      obtain ⟨mv,hm,rfl⟩ := List.mem_map.mp hx
      exact (ih mv _).mpr (allMoves_sound _ hk mv)

/-- Only the original query-time and blank-delay scores are folded. We do
    not reevaluate any tape trace, cycle certificate, or FAR proof. -/
def partialScore (p : PartialMachine) : (t : PartialAudit) → Nat
  | .unresolved => 0
  | .closed a => auditScore p a
  | .split n s kids =>
      max (queryScore p n s)
        (maxList (moves.map fun mv =>
          partialScore (refine p s (some mv)) (kids mv)))
termination_by structural t => t

theorem partial_score_le_partialWeights (p : PartialMachine)
    (t : PartialAudit) (B : Nat) :
    partialScore p t ≤ B ↔ partialWeights B p t = true := by
  induction t generalizing p with
  | unresolved => simp [partialScore, partialWeights]
  | closed a => exact audit_score_le_weightAudit p a B
  | split n s kids ih =>
    simp only [partialScore, partialWeights, Nat.max_le, Bool.and_eq_true, maxList_le]
    constructor
    · rintro ⟨hq,hk⟩
      refine ⟨(quick_weight_iff B p n s).mpr ((queryScore_le p n s B).mp hq),
        allMoves_of _ ?_⟩
      intro mv
      exact (ih mv _).mp (hk _ (List.mem_map.mpr ⟨mv,mem_moves mv,rfl⟩))
    · rintro ⟨hq,hk⟩
      refine ⟨(queryScore_le p n s B).mpr ((quick_weight_iff B p n s).mp hq), ?_⟩
      intro x hx
      obtain ⟨mv,hm,rfl⟩ := List.mem_map.mp hx
      exact (ih mv _).mpr (allMoves_sound _ hk mv)

/-- Least-bound criterion under *explicit* B-bounds on the residuals. -/
theorem partial_score_exact (A B : Nat) (p : PartialMachine)
    (t : PartialAudit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (old : partialCheck A p t = true)
    (hres : ∀ e ∈ partialResiduals p t,
      ∀ m, compatible e.2 m → WeightedBound B m) :
    (∀ m, compatible p m → WeightedBound B m) ↔
      partialScore p t ≤ B :=
  (partial_weights_exact A B p t hroot hno old hres).trans
    (partial_score_le_partialWeights p t B).symm

/-- When all unresolved cylinders are nonhalting (hence bounded at *every*
    threshold), the computed positive score is actually attained by a
    compatible halting machine. This is a genuine sharp whole-cylinder
    theorem rather than just a nonhalting-or-bounded dichotomy. -/
theorem score_attained (A : Nat) (p : PartialMachine)
    (t : PartialAudit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (old : partialCheck A p t = true)
    (hres_all : ∀ B, ∀ e ∈ partialResiduals p t,
      ∀ m, compatible e.2 m → WeightedBound B m)
    (hpos : 0 < partialScore p t) :
    ∃ m, compatible p m ∧ ∃ k d, HaltsAfter m k ∧
      d ∈ delays (zeroNext m) 0 ∧ d + k + 1 = partialScore p t := by
  classical
  let S := partialScore p t
  have hupper : ∀ m, compatible p m → WeightedBound S m :=
    (partial_score_exact A S p t hroot hno old (hres_all S)).mpr (Nat.le_refl _)
  have hnot : ¬ ∀ m, compatible p m → WeightedBound (S - 1) m := by
    intro hb
    have hle :=
      (partial_score_exact A (S - 1) p t hroot hno old (hres_all (S - 1))).mp hb
    omega
  apply Classical.byContradiction
  intro hnone
  apply hnot
  intro m hm k d hk hd
  have hu := hupper m hm k d hk hd
  have hn : d + k + 1 ≠ S :=
    fun he => hnone ⟨m,hm,k,d,hk,hd,he⟩
  omega

#print axioms quick_weight_iff
#print axioms audit_score_le_weightAudit
#print axioms partial_score_le_partialWeights
#print axioms partial_score_exact
#print axioms score_attained

end BB6.Agent11PartialWeightScore
