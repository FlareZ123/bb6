import FourHoleRootFrontier
import TNFPilot
import SideCycle
import AlternatingResidualSweep

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31FourHoleRoster

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6Coverage.Agent50SideCycle
open BB6.Agent31FourHoleFrontier

theorem OpenLeaf.mem_residuals {p : PartialMachine} {f : RootedFrontier 395 p}
    {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    (address, q) ∈ residuals f := by
  induction h with
  | here path =>
      simp [residuals]
  | @child p n c path hrun hhole hweight children mv address q hchild ih =>
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address, q), ih, rfl⟩

inductive ResidualNonhaltWitness where
  | ray (n : Nat) (right : Bool) (mask : Nat)
  | lasso (n : Nat)
  | side (entry period : Nat) (right : Bool) (boundary : Int)
  | alternating (w : Bool)

def residualMask (mask : Nat) (q : Fin 6) : Bool := mask.testBit q.val

/-- Exact finite table equality, without hash-based identity. -/
def sameTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun state =>
    [false, true].all fun symbol =>
      decide (p (state, symbol) = q (state, symbol))

theorem sameTable_sound {p q : PartialMachine}
    (h : sameTable p q = true) : p = q := by
  funext s
  rcases s with ⟨state, symbol⟩
  have h1 :
      (List.finRange 6).all (fun q' =>
        [false, true].all fun b =>
          decide (p (q', b) = q (q', b))) = true := by
    simpa [sameTable] using h
  have h2 := List.all_eq_true.mp h1 state (List.mem_finRange state)
  have h3 := List.all_eq_true.mp h2 symbol (by cases symbol <;> simp)
  exact of_decide_eq_true h3

def residualWitnessOK (p : PartialMachine) : ResidualNonhaltWitness → Bool
  | .ray n right mask => finiteRayCheck p n right (residualMask mask)
  | .lasso n => finiteLassoCheck p n
  | .side entry period right boundary =>
      decide (0 < period) && finiteSideCycleCheck p entry period right boundary
  | .alternating w =>
      decide (sameTable p (BB6Coverage.Agent50AlternatingSweep.table w))

theorem residualWitnessOK_sound (p : PartialMachine)
    (w : ResidualNonhaltWitness) (h : residualWitnessOK p w = true) :
    ∀ m, compatible p m → NeverHalts m := by
  cases w with
  | ray n right mask =>
      exact zeroCover_never
        (finiteRayCheck_sound p n right (residualMask mask) 0 h)
  | lasso n =>
      exact zeroCover_never (finiteLassoCheck_sound p n 0 h)
  | side entry period right boundary =>
      have hc : 0 < period ∧
          finiteSideCycleCheck p entry period right boundary = true := by
        simpa only [residualWitnessOK, Bool.and_eq_true, decide_eq_true_eq] using h
      exact finiteSideCycleCheck_sound p entry period right boundary hc.1 hc.2
  | alternating w =>
      have hc : sameTable p (BB6Coverage.Agent50AlternatingSweep.table w) = true := by
        simpa [residualWitnessOK] using h
      rw [sameTable_sound hc]
      exact BB6Coverage.Agent50AlternatingSweep.never w

/-- The 37 checked witnesses that lie in the seven-edge frontier. These are
    reindexed from the exact 207-entry pilot roster after removing the
    depth-eight and depth-nine continuation now closed by the four-hole
    certificate. -/
def residualWitnessIndices : List (Nat × ResidualNonhaltWitness) :=
  [(1,.ray 0 true 3), (3,.ray 0 true 3), (5,.ray 0 true 3), (7,.ray 0 true 3),
   (12,.ray 0 true 7), (14,.ray 0 true 7), (16,.ray 0 true 7), (18,.ray 0 true 7),
   (20,.ray 0 true 7), (22,.ray 0 true 7), (25,.ray 0 true 15), (27,.ray 0 true 15),
   (29,.ray 0 true 15), (31,.ray 0 true 15), (32,.lasso 4), (33,.ray 0 true 15),
   (35,.ray 0 true 15), (37,.ray 0 true 15), (50,.ray 7 false 8), (51,.ray 17 false 8),
   (52,.ray 7 false 8), (74,.ray 13 false 8), (75,.ray 11 false 8), (76,.lasso 8),
   (89,.lasso 9), (90,.ray 10 false 8), (94,.ray 9 false 8), (96,.ray 9 false 8),
   (116,.lasso 7), (130,.ray 0 true 15),
   (24,.side 0 4 true (0)), (28,.side 1 3 true (1)), (53,.side 6 3 true (2)),
   (62,.side 0 10 true (0)), (64,.side 0 10 true (0)),
   (65,.side 8 7 false (1)), (84,.side 7 3 false (1))]

noncomputable def residualWitnessRoster :
    List ((List Move × PartialMachine) × ResidualNonhaltWitness) :=
  residualWitnessIndices.filterMap fun (i, w) =>
    (residuals rootFrontier)[i]?.map fun e => (e, w)

theorem residualWitnessRoster_count : residualWitnessRoster.length = 37 := by
  decide

theorem residualWitnessRoster_checked :
    residualWitnessRoster.all (fun e => residualWitnessOK e.1.2 e.2) = true := by
  decide

noncomputable def residualHasWitness (q : PartialMachine) : Bool :=
  residualWitnessRoster.any fun e => decide (sameTable e.1.2 q)

theorem residualHasWitness_sound (q : PartialMachine)
    (h : residualHasWitness q = true) :
    ∀ m, compatible q m → WeightedBound 395 m := by
  rcases List.any_eq_true.mp h with ⟨e, hmem, heq⟩
  rcases e with ⟨(address, p), w⟩
  have hsame : sameTable p q = true := of_decide_eq_true heq
  have hp : p = q := sameTable_sound hsame
  subst p
  have hc := List.all_eq_true.mp residualWitnessRoster_checked ((address, q), w) hmem
  intro m hm
  exact weighted_never 395 m (residualWitnessOK_sound q w hc m hm)

noncomputable def remainingRootRoster : List (List Move × PartialMachine) :=
  (residuals rootFrontier).filter fun e => !residualHasWitness e.2

/-- A 124-cylinder firstOneCylinder frontier at weighted bound 395. The
    37 explicit nonhalting witnesses discharge 37 of the 161 off-path leaves;
    the four-hole certificate closes the entire depth-seven continuation. -/
theorem remainingRootRoster_count : remainingRootRoster.length = 124 := by
  decide

theorem remainingRootRoster_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 395 m ∨
        ∃ e ∈ remainingRootRoster, compatible e.2 m := by
  intro m hm
  rcases RootedFrontier.sound rootFrontier m hm with hbound | ⟨address, q, hopen, hcomp⟩
  · exact Or.inl hbound
  · have hmem : (address, q) ∈ residuals rootFrontier :=
      OpenLeaf.mem_residuals hopen
    cases hw : residualHasWitness q with
    | true =>
        exact Or.inl (residualHasWitness_sound q hw m hcomp)
    | false =>
        exact Or.inr ⟨(address, q),
          List.mem_filter.mpr ⟨hmem, by simp [hw]⟩, hcomp⟩

#print axioms residualWitnessRoster_checked
#print axioms remainingRootRoster_count
#print axioms remainingRootRoster_sound

end BB6.Agent31FourHoleRoster
