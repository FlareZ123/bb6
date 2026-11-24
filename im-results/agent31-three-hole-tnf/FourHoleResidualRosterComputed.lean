import FourHoleResidualRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31FourHoleRosterComputed

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent8TNFPath

/-- Compute the off-path residual cylinders from the validated first-hole path
    alone. Unlike the proof-carrying RootedFrontier object, this finite list
    does not capture its noncomputable weighted certificate. -/
def enumerateResiduals (p : PartialMachine) :
    List PathEntry → List (List Move × PartialMachine)
  | [] => []
  | (_, s, mv) :: xs =>
      allMoves.flatMap fun actual =>
        if actual = mv then
          (enumerateResiduals (refine p s (some mv)) xs).map
            fun (address, q) => (actual :: address, q)
        else
          [([actual], refine p s (some actual))]

/-- The list projection of buildFrontierB is exactly the computable path
    enumeration. The weighted certificate affects only the closed terminal
    node, whose residual projection is empty. -/
theorem buildFrontierB_residuals (B : Nat) (p : PartialMachine) (cut : Nat)
    (hp : RawRootPath p) (xs : List PathEntry)
    (h : pathOKB B p cut xs = true)
    (cert : WeightedTNFCertificate B (pathEnd p cut xs).1 6) :
    residuals (buildFrontierB B p cut hp xs h cert) =
      enumerateResiduals p xs := by
  induction xs generalizing p cut hp with
  | nil =>
      simp [buildFrontierB, residuals, enumerateResiduals]
  | cons entry xs ih =>
      rcases entry with ⟨n, s, mv⟩
      have hfields := pathOKB_cons h
      rcases hfields with ⟨hhole, hread, _, _, hweight, htail⟩
      let c := (extractRunConfig hread).val
      have hr : knownRun p n = some c := (extractRunConfig hread).property
      have hs : readSlot c = s := by
        have h' : (some c).map readSlot = some s := by
          simpa [hr] using hread
        simpa using h'
      have hhole' : p (readSlot c) = none := by
        simpa [hs] using hhole
      have hw : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
          d + n + 1 ≤ B := by
        simpa [hs.symm] using (weightOK_sound p s n B hweight)
      have htail' : pathOKB B (refine p (readSlot c) (some mv))
          (advanceCut cut mv) xs = true := by
        simpa [hs.symm] using htail
      have cert' : WeightedTNFCertificate B
          (pathEnd (refine p (readSlot c) (some mv)) (advanceCut cut mv) xs).1 6 := by
        simpa [pathEnd, hs.symm] using cert
      have hp' : RawRootPath (refine p (readSlot c) (some mv)) :=
        RawRootPath.step (mv := mv) hp hr hhole'
      have ih' := ih (refine p (readSlot c) (some mv)) (advanceCut cut mv) hp' htail' cert'
      simp [buildFrontierB, residuals, enumerateResiduals, hs, ih']

/-- The computable enumeration agrees exactly with the certified frontier's
    residual projection. -/
theorem rootFrontier_residuals :
    residuals rootFrontier = enumerateResiduals root (path.take 7) := by
  simpa [rootFrontier] using
    (buildFrontierB_residuals 395 root 2 RawRootPath.root
      (path.take 7) path_prefix_checked wideCertificate_root)

/-- The 37 source-checked witness records, indexed in the same stable order as
    the original 161-leaf frontier, but now backed by computable list data. -/
def enumeratedWitnessRoster :
    List ((List Move × PartialMachine) × ResidualNonhaltWitness) :=
  residualWitnessIndices.filterMap fun (i, w) =>
    (enumerateResiduals root (path.take 7))[i]?.map fun e => (e, w)

theorem enumeratedWitnessRoster_count : enumeratedWitnessRoster.length = 37 := by
  decide

theorem enumeratedWitnessRoster_checked :
    enumeratedWitnessRoster.all
      (fun e => residualWitnessOK e.1.2 e.2) = true := by
  decide

def enumeratedResidualHasWitness (q : PartialMachine) : Bool :=
  enumeratedWitnessRoster.any fun e => decide (sameTable e.1.2 q)

theorem enumeratedResidualHasWitness_sound (q : PartialMachine)
    (h : enumeratedResidualHasWitness q = true) :
    ∀ m, compatible q m → WeightedBound 395 m := by
  rcases List.any_eq_true.mp h with ⟨e, hmem, heq⟩
  have hsame : sameTable e.1.2 q = true := of_decide_eq_true heq
  have hp : e.1.2 = q := sameTable_sound hsame
  have hc := List.all_eq_true.mp enumeratedWitnessRoster_checked e hmem
  rw [hp] at hc
  intro m hm
  exact weighted_never 395 m
    (residualWitnessOK_sound q e.2 hc m hm)

/-- A fully computable 124-cylinder residual roster. -/
def enumeratedRemainingRootRoster : List (List Move × PartialMachine) :=
  (enumerateResiduals root (path.take 7)).filter
    fun e => !enumeratedResidualHasWitness e.2

theorem enumeratedRemainingRootRoster_count :
    enumeratedRemainingRootRoster.length = 124 := by
  decide

/-- Every authentic first-one completion is either already below weighted
    bound 395 or belongs to one of the explicit computable residual cylinders. -/
theorem enumeratedRemainingRootRoster_sound :
    ∀ m, compatible root m →
      WeightedBound 395 m ∨
        ∃ e ∈ enumeratedRemainingRootRoster, compatible e.2 m := by
  intro m hm
  rcases RootedFrontier.sound rootFrontier m hm with hbound | ⟨address, q, hopen, hcomp⟩
  · exact Or.inl hbound
  · have hmem0 : (address, q) ∈ residuals rootFrontier :=
      OpenLeaf.mem_residuals hopen
    have hmem : (address, q) ∈ enumerateResiduals root (path.take 7) := by
      simpa [rootFrontier_residuals] using hmem0
    cases hw : enumeratedResidualHasWitness q with
    | true =>
        exact Or.inl (enumeratedResidualHasWitness_sound q hw m hcomp)
    | false =>
        exact Or.inr ⟨(address, q),
          List.mem_filter.mpr ⟨hmem, by simp [hw]⟩, hcomp⟩

#print axioms buildFrontierB_residuals
#print axioms enumeratedWitnessRoster_checked
#print axioms enumeratedRemainingRootRoster_count
#print axioms enumeratedRemainingRootRoster_sound

end BB6.Agent31FourHoleRosterComputed
