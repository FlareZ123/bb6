import FourHoleResidualRoster
import WeightedTNF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent47RootSiblingSweep

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50TNFPilot

/-- The 19 still-open B0 siblings at the root first-one cylinder. -/
def rootLevelMoves : List Move :=
  [⟨false, false, 0⟩,
   ⟨true, false, 0⟩,
   ⟨false, false, 1⟩,
   ⟨true, false, 1⟩,
   ⟨false, false, 2⟩,
   ⟨false, true, 2⟩,
   ⟨true, false, 2⟩,
   ⟨false, false, 3⟩,
   ⟨false, true, 3⟩,
   ⟨true, false, 3⟩,
   ⟨true, true, 3⟩,
   ⟨false, false, 4⟩,
   ⟨false, true, 4⟩,
   ⟨true, false, 4⟩,
   ⟨true, true, 4⟩,
   ⟨false, false, 5⟩,
   ⟨false, true, 5⟩,
   ⟨true, false, 5⟩,
   ⟨true, true, 5⟩]

structure RootSiblingWitness where
  parent : Move
  child : Move
  witness : ResidualNonhaltWitness

/-- Bounded-search candidates. The `rootSiblingWitnessesOK` theorem below
    replays every candidate with the kernel-computable residual checker. -/
def rootSiblingWitnesses : List RootSiblingWitness :=
 [
  { parent := ⟨false, false, 0⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 0⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 0⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 0⟩, child := ⟨false, false, 1⟩, witness := .side 0 4 false (1 : Int) },
  { parent := ⟨false, false, 0⟩, child := ⟨false, true, 1⟩, witness := .lasso 4 },
  { parent := ⟨false, false, 0⟩, child := ⟨true, false, 1⟩, witness := .side 0 4 false (1 : Int) },
  { parent := ⟨false, false, 0⟩, child := ⟨true, true, 1⟩, witness := .lasso 3 },
  { parent := ⟨true, false, 0⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨true, false, 0⟩, child := ⟨false, true, 0⟩, witness := .side 0 4 true (0 : Int) },
  { parent := ⟨true, false, 0⟩, child := ⟨true, true, 0⟩, witness := .side 0 4 true (0 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨false, false, 1⟩, witness := .side 3 1 false (-1 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨false, true, 1⟩, witness := .side 3 1 false (1 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨true, false, 1⟩, witness := .side 3 1 false (-1 : Int) },
  { parent := ⟨false, false, 1⟩, child := ⟨true, true, 1⟩, witness := .lasso 3 },
  { parent := ⟨true, false, 1⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨true, false, 1⟩, child := ⟨false, false, 1⟩, witness := .side 3 1 false (-1 : Int) },
  { parent := ⟨true, false, 1⟩, child := ⟨false, true, 1⟩, witness := .side 4 1 false (2 : Int) },
  { parent := ⟨true, false, 1⟩, child := ⟨true, false, 1⟩, witness := .side 3 1 false (-1 : Int) },
  { parent := ⟨true, false, 1⟩, child := ⟨true, true, 1⟩, witness := .side 1 3 true (0 : Int) },
  { parent := ⟨false, false, 2⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 2⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 2⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 2⟩, child := ⟨true, true, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 2⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 2⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 2⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 2⟩, child := ⟨false, false, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 2⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 2⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 2⟩, child := ⟨false, true, 2⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨false, true, 2⟩, child := ⟨true, true, 2⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, false, 2⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 3⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 3⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 3⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 3⟩, child := ⟨true, true, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 3⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 3⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 3⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 3⟩, child := ⟨false, false, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 3⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 3⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 3⟩, child := ⟨false, true, 3⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨false, true, 3⟩, child := ⟨true, true, 3⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, false, 3⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨true, true, 3⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨true, true, 3⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨true, true, 3⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨true, true, 3⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨true, true, 3⟩, child := ⟨false, true, 3⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, true, 3⟩, child := ⟨true, true, 3⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨false, false, 4⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 4⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 4⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 4⟩, child := ⟨true, true, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 4⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 4⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 4⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 4⟩, child := ⟨false, false, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 4⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 4⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 4⟩, child := ⟨false, true, 4⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨false, true, 4⟩, child := ⟨true, true, 4⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, false, 4⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨true, true, 4⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨true, true, 4⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨true, true, 4⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨true, true, 4⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨true, true, 4⟩, child := ⟨false, true, 4⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, true, 4⟩, child := ⟨true, true, 4⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨false, false, 5⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨false, false, 5⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 5⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, false, 5⟩, child := ⟨true, true, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 5⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 5⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 5⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨false, true, 5⟩, child := ⟨false, false, 1⟩, witness := .lasso 3 },
  { parent := ⟨false, true, 5⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 5⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨false, true, 5⟩, child := ⟨false, true, 5⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨false, true, 5⟩, child := ⟨true, true, 5⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, false, 5⟩, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { parent := ⟨true, true, 5⟩, child := ⟨false, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨true, true, 5⟩, child := ⟨true, true, 0⟩, witness := .side 0 3 true (0 : Int) },
  { parent := ⟨true, true, 5⟩, child := ⟨false, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨true, true, 5⟩, child := ⟨true, true, 1⟩, witness := .side 1 2 true (1 : Int) },
  { parent := ⟨true, true, 5⟩, child := ⟨false, true, 5⟩, witness := .side 2 1 true (2 : Int) },
  { parent := ⟨true, true, 5⟩, child := ⟨true, true, 5⟩, witness := .side 2 1 true (2 : Int) }
 ]

def rootSiblingParent (parent : Move) : PartialMachine :=
  refine BB6.Agent50TNFPilot.root (1, false) (some parent)

def rootSiblingAfterTwo (parent : Move) : Config :=
  (knownRun (rootSiblingParent parent) 2).getD blank

theorem rootSiblingKnownRunTwo (parent : Move) :
    knownRun (rootSiblingParent parent) 2 = some (rootSiblingAfterTwo parent) := by
  simp [rootSiblingAfterTwo, knownRun, knownStep, rootSiblingParent,
    refine, BB6.Agent50TNFPilot.root, blank, readSlot, applyMove]

def rootSiblingChild (parent child : Move) : PartialMachine :=
  refine (rootSiblingParent parent) (readSlot (rootSiblingAfterTwo parent)) (some child)

/-- Every proposed lasso/side-cycle certificate is checked by the existing
    finite checker, not trusted from the generating simulation. -/
theorem rootSiblingWitnessesOK :
    rootSiblingWitnesses.all
      (fun w => residualWitnessOK (rootSiblingChild w.parent w.child) w.witness) = true := by
  decide

def rootSiblingIsClosed (parent child : Move) : Bool :=
  rootSiblingWitnesses.any
    (fun w => decide (w.parent = parent ∧ w.child = child))

theorem rootSiblingIsClosed_sound (parent child : Move)
    (h : rootSiblingIsClosed parent child = true) :
    ∀ m, compatible (rootSiblingChild parent child) m → NeverHalts m := by
  have hmem : ∃ w ∈ rootSiblingWitnesses,
      decide (w.parent = parent ∧ w.child = child) = true :=
    List.any_eq_true.mp h
  rcases hmem with ⟨w, hw, hpair⟩
  have hOK : residualWitnessOK (rootSiblingChild w.parent w.child) w.witness :=
    (List.all_eq_true.mp rootSiblingWitnessesOK) w hw
  have hpair' : w.parent = parent ∧ w.child = child := of_decide_eq_true hpair
  rcases hpair' with ⟨rfl, rfl⟩
  exact residualWitnessOK_sound (rootSiblingChild w.parent w.child) w.witness hOK

def rootSiblingOpenMoves (parent : Move) : List Move :=
  allMoves.filter (fun child => !(rootSiblingIsClosed parent child))

def rootSiblingResidualRoster : List (List Move × PartialMachine) :=
  rootLevelMoves.flatMap fun parent =>
    (rootSiblingOpenMoves parent).map fun child =>
      ([parent, child], rootSiblingChild parent child)

def rootSiblingFirstHoleCheck (parent : Move) : Bool :=
  decide (rootSiblingParent parent (readSlot (rootSiblingAfterTwo parent)) = none)

theorem rootSiblingFirstHoleChecks :
    rootLevelMoves.all rootSiblingFirstHoleCheck = true := by
  decide

theorem rootSiblingFirstHole (parent : Move) (hp : parent ∈ rootLevelMoves) :
    rootSiblingParent parent (readSlot (rootSiblingAfterTwo parent)) = none := by
  have h := (List.all_eq_true.mp rootSiblingFirstHoleChecks) parent hp
  exact of_decide_eq_true (by simpa [rootSiblingFirstHoleCheck] using h)

def rootSiblingHaltWeightCheck (parent : Move) : Bool :=
  decide (∀ d ∈ possibleDelays
    (refine (rootSiblingParent parent) (readSlot (rootSiblingAfterTwo parent)) none) 0,
      d + 2 + 1 ≤ 7014)

theorem rootSiblingHaltWeightChecks :
    rootLevelMoves.all rootSiblingHaltWeightCheck = true := by
  decide

theorem rootSiblingHaltWeight (parent : Move) (hp : parent ∈ rootLevelMoves) :
    ∀ d ∈ possibleDelays
      (refine (rootSiblingParent parent) (readSlot (rootSiblingAfterTwo parent)) none) 0,
        d + 2 + 1 ≤ 7014 := by
  have h := (List.all_eq_true.mp rootSiblingHaltWeightChecks) parent hp
  exact of_decide_eq_true (by simpa [rootSiblingHaltWeightCheck] using h)

theorem rootSiblingParent_root (parent : Move) :
    rootSiblingParent parent initialSlot = some (some ⟨true, true, 1⟩) := by
  simp [rootSiblingParent, refine, BB6.Agent50TNFPilot.root, initialSlot]

/-- Exact first-hole dichotomy for each of the 19 ten-hole root siblings. -/
theorem rootSiblingParent_sound (parent : Move) (hp : parent ∈ rootLevelMoves)
    (m : Machine) (hm : compatible (rootSiblingParent parent) m) :
    WeightedBound 7014 m ∨
      ∃ child ∈ rootSiblingOpenMoves parent, compatible (rootSiblingChild parent child) m := by
  let s := readSlot (rootSiblingAfterTwo parent)
  cases hslot : m s with
  | none =>
      have hc : compatible (refine (rootSiblingParent parent) s none) m := by
        simpa [s, hslot] using compatible_refine (rootSiblingParent parent) m s hm
      exact Or.inl (first_hole_weighted_halt 7014 (rootSiblingParent parent) 2
        (rootSiblingAfterTwo parent) (rootSiblingParent_root parent)
        (rootSiblingKnownRunTwo parent) (rootSiblingFirstHole parent hp)
        (rootSiblingHaltWeight parent hp) m hc)
  | some child =>
      have hc : compatible (rootSiblingChild parent child) m := by
        simpa [rootSiblingChild, s, hslot] using
          compatible_refine (rootSiblingParent parent) m s hm
      cases hclosed : rootSiblingIsClosed parent child with
      | true =>
          exact Or.inl (weighted_never 7014 m
            (rootSiblingIsClosed_sound parent child hclosed m hc))
      | false =>
          exact Or.inr ⟨child, List.mem_filter.mpr
            ⟨allMoves_complete child, by simp [rootSiblingOpenMoves, hclosed]⟩, hc⟩

/-- The union of the 19 root-sibling expansions: every completion in one
    of these root cylinders is bounded or lies in one of 364 explicit
    nine-hole residual cylinders. -/
theorem rootSiblingExpansion_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m)
    (parent : Move) (hp : parent ∈ rootLevelMoves)
    (hB0 : m (1, false) = some parent) :
    WeightedBound 7014 m ∨
      ∃ e ∈ rootSiblingResidualRoster, compatible e.2 m := by
  have hp' : compatible (rootSiblingParent parent) m := by
    simpa [rootSiblingParent, hB0] using
      compatible_refine BB6.Agent50TNFPilot.root m (1, false) hm
  rcases rootSiblingParent_sound parent hp m hp' with hBound | ⟨child, hchild, hc⟩
  · exact Or.inl hBound
  · exact Or.inr ⟨([parent, child], rootSiblingChild parent child),
      List.mem_flatMap.mpr
        ⟨parent, hp, List.mem_map.mpr ⟨child, hchild, rfl⟩⟩, hc⟩

theorem rootLevelMoves_count : rootLevelMoves.length = 19 := by
  decide

theorem rootSiblingWitnesses_count : rootSiblingWitnesses.length = 92 := by
  decide

theorem rootSiblingResidualRoster_count : rootSiblingResidualRoster.length = 364 := by
  decide

/-- Exact completion-mass accounting for the 19 first-hole expansions:
    92 nonhalting ordinary children, 19 halt children, 364 open ordinary
    children, each child cylinder having nine undefined rows. -/
theorem rootSibling_mass_partition :
    rootSiblingResidualRoster.length * 25^9 +
      rootSiblingWitnesses.length * 25^9 +
      rootLevelMoves.length * 25^9 =
      rootLevelMoves.length * 25^10 := by
  rw [rootSiblingResidualRoster_count, rootSiblingWitnesses_count, rootLevelMoves_count]
  norm_num [pow_succ]

#print axioms rootSiblingWitnessesOK
#print axioms rootSiblingIsClosed_sound
#print axioms rootSiblingFirstHole
#print axioms rootSiblingHaltWeight
#print axioms rootSiblingParent_sound
#print axioms rootSiblingExpansion_sound
#print axioms rootSiblingResidualRoster_count
#print axioms rootSibling_mass_partition

end BB6.Agent47RootSiblingSweep
