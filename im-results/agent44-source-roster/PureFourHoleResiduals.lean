import RootFrontier
import FourHoleRootFrontier
import FourHoleResidualRoster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent44SourceRoster

open BB6Coverage
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier

/-- Pure projection of the off-path residual leaves of buildFrontierB.
    It depends only on the concrete path entries and ordinary move list,
    not on the weighted certificate carried by the closed terminal node. -/
def pureResiduals (p : PartialMachine) : List PathEntry →
    List (List Move × PartialMachine)
  | [] => []
  | (n, s, mv) :: xs =>
      allMoves.flatMap fun actual =>
        if actual = mv then
          (pureResiduals (refine p s (some mv)) xs).map
            (fun (address, q) => (actual :: address, q))
        else
          [([actual], refine p s (some actual))]

/-- The residual projection of the proof-carrying frontier is exactly the
    pure path expansion. The proof payload (including the four-hole
    certificate) is irrelevant to the finite table list. -/
theorem residuals_buildFrontierB (B : Nat) :
    ∀ (p : PartialMachine) (cut : Nat) (hp : RawRootPath p)
      (xs : List PathEntry)
      (h : pathOKB B p cut xs = true)
      (cert : WeightedTNFCertificate B (pathEnd p cut xs).1 6),
      residuals (buildFrontierB B p cut hp xs h cert) = pureResiduals p xs := by
  intro p cut hp xs
  induction xs generalizing p cut hp with
  | nil =>
      intro h cert
      simp [buildFrontierB, residuals, pureResiduals]
  | cons entry xs ih =>
      rcases entry with ⟨n, s, mv⟩
      intro h cert
      simp [buildFrontierB, residuals, pureResiduals, ih]

theorem rootFrontier_residuals_eq :
    residuals rootFrontier = pureResiduals BB6.Agent50TNFPilot.root (path.take 7) := by
  exact residuals_buildFrontierB 395 root 2 RawRootPath.root
    (path.take 7) path_prefix_checked wideCertificate_root

/-- The 37 witness entries, reindexed against the pure residual list rather
    than the noncomputable proof-carrying frontier. -/
def pureResidualWitnessRoster :
    List ((List Move × PartialMachine) × ResidualNonhaltWitness) :=
  residualWitnessIndices.filterMap fun (i, w) =>
    (pureResiduals BB6.Agent50TNFPilot.root (path.take 7))[i]?.map fun e => (e, w)

theorem residualWitnessRoster_eq_pure :
    residualWitnessRoster = pureResidualWitnessRoster := by
  unfold residualWitnessRoster pureResidualWitnessRoster
  rw [rootFrontier_residuals_eq]

def pureResidualHasWitness (q : PartialMachine) : Bool :=
  pureResidualWitnessRoster.any fun e => decide (sameTable e.1.2 q)

theorem residualHasWitness_eq_pure (q : PartialMachine) :
    residualHasWitness q = pureResidualHasWitness q := by
  simp [residualHasWitness, pureResidualHasWitness, residualWitnessRoster_eq_pure]

/-- Pure, executable version of Agent31's 124-table residual roster. -/
def pureRemainingRootRoster : List (List Move × PartialMachine) :=
  (pureResiduals root (path.take 7)).filter fun e =>
    !pureResidualHasWitness e.2

theorem remainingRootRoster_eq_pure :
    remainingRootRoster = pureRemainingRootRoster := by
  unfold remainingRootRoster pureRemainingRootRoster
  rw [rootFrontier_residuals_eq]
  simp [residualHasWitness_eq_pure]

theorem pureRemainingRootRoster_count :
    pureRemainingRootRoster.length = 124 := by
  rw [← remainingRootRoster_eq_pure]
  exact remainingRootRoster_count

theorem pureRemainingRootRoster_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 395 m ∨
        ∃ e ∈ pureRemainingRootRoster, compatible e.2 m := by
  intro m hm
  rcases BB6.Agent31FourHoleRoster.remainingRootRoster_sound m hm with hbound | ⟨e, he, hcomp⟩
  · exact Or.inl hbound
  · exact Or.inr ⟨e, by simpa [remainingRootRoster_eq_pure] using he, hcomp⟩

#print axioms residuals_buildFrontierB
#print axioms rootFrontier_residuals_eq
#print axioms pureRemainingRootRoster_count
#print axioms pureRemainingRootRoster_sound

end BB6.Agent44SourceRoster
