import RootFrontierR1R4
import HardRootParents
import CanonicalRaw114Accepted
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50CanonicalR4Ingestion

open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent50TNFPilot
open BB6.Agent50RootFrontier
open BB6.Agent47RootedTNF
open BB6.Agent19HardRoot
open BB6.Agent47CanonicalRaw114Accepted
open BB6.Agent47CanonicalRefinement

abbrev p23 : PartialMachine := BB6.Agent19HardRoot.p23

/-- The r4 source path enters exactly the canonical-77 raw23 parent after
    its first two first-hole refinements. -/
theorem r4AfterSecond_eq_p23 : r4AfterSecond = p23 := by
  rfl

/-- Re-root the already checked r4 branch at its exact canonical parent.
    This reuses the source-connected r4 certificate and keeps all seven
    off-path sibling layers explicit. -/
noncomputable def r4Subtree : RootedFrontier 7014 p23 := by
  change RootedFrontier 7014 r4AfterSecond
  have hp := pathOKB_cons r4PathOK
  rcases hp with ⟨_,hread1,_,_,_,htail1⟩
  let c1 := (extractRunConfig hread1).val
  have hr1 : knownRun root 1 = some c1 := (extractRunConfig hread1).property
  have hs1 : readSlot c1 = (1,false) := by
    have h' : (some c1).map readSlot = some (1,false) := by
      simpa [hr1] using hread1
    simpa using h'
  have hhole1' : root (readSlot c1) = none := by
    simpa [hs1] using (show root (1,false) = none by decide)
  have raw1 : RawRootPath pilotStart := by
    simpa [pilotStart, pilotFirst, hs1] using
      (RawRootPath.step (mv := pilotFirst) RawRootPath.root hr1 hhole1')
  have r4Tail1 : pathOKB 7014 pilotStart pilotCut r4.path.tail = true := by
    simpa [pilotStart, pilotFirst, pilotCut, hs1, r4] using htail1
  have hp2 := pathOKB_cons r4Tail1
  rcases hp2 with ⟨_,hread2,_,_,_,htail2⟩
  let c2 := (extractRunConfig hread2).val
  have hr2 : knownRun pilotStart 2 = some c2 := (extractRunConfig hread2).property
  have hs2 : readSlot c2 = (2,false) := by
    have h' : (some c2).map readSlot = some (2,false) := by
      simpa [hr2] using hread2
    simpa using h'
  have hhole2' : pilotStart (readSlot c2) = none := by
    simpa [hs2] using (show pilotStart (2,false) = none by decide)
  have rawR4Second : RawRootPath r4AfterSecond := by
    simpa [r4AfterSecond, r4Second, hs2] using
      (RawRootPath.step (mv := r4Second) raw1 hr2 hhole2')
  have r4Tail2 : pathOKB 7014 r4AfterSecond r4AfterSecondCut
      r4.path.tail.tail = true := by
    simpa [r4AfterSecond, r4Second, pilotStart, pilotFirst,
      r4AfterSecondCut, hs1, hs2, r4] using htail2
  have r4CertTail : WeightedTNFCertificate 7014
      (pathEnd r4AfterSecond r4AfterSecondCut r4.path.tail.tail).1 6 := by
    rw [← r4_pathEnd_tail2]
    exact r4Cert
  exact buildFrontierB 7014 r4AfterSecond r4AfterSecondCut rawR4Second
    r4.path.tail.tail r4Tail2 r4CertTail

/-- A finite full 24-ary frontier has 23 residual-or-closed leaves per
    expansion, plus its single root leaf. This avoids evaluating a large
    dependent frontier merely to count its residual list. -/
private theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map f).sum + (xs.map g).sum =
      (xs.map (fun x => f x + g x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem sum_map_mul_add_one {α : Type} (xs : List α) (f : α → Nat) :
    (xs.map (fun x => 23 * f x + 1)).sum =
      23 * (xs.map f).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

theorem residuals_closed_expanded {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) :
    (residuals f).length + closedLeaves f = 23 * expandedNodes f + 1 := by
  induction f with
  | residual path =>
      simp [residuals, closedLeaves, expandedNodes]
  | closed path cert =>
      simp [residuals, closedLeaves, expandedNodes]
  | @expand p n c path hrun hhole hweight children ih =>
      let f := fun mv : Move => (residuals (children mv)).length
      let g := fun mv : Move => closedLeaves (children mv)
      let h := fun mv : Move => expandedNodes (children mv)
      have hsum :
          (allMoves.map (fun mv => f mv + g mv)).sum =
            (allMoves.map (fun mv => 23 * h mv + 1)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro mv hmem
        exact ih mv
      have hlen :
          (residuals (.expand path hrun hhole hweight children)).length =
            (allMoves.map f).sum := by
        simp [residuals, f, List.length_flatMap, List.length_map]
      rw [hlen]
      change (allMoves.map f).sum + (allMoves.map g).sum =
        23 * (1 + (allMoves.map h).sum) + 1
      calc
        (allMoves.map f).sum + (allMoves.map g).sum =
            (allMoves.map (fun mv => f mv + g mv)).sum :=
          sum_map_add allMoves f g
        _ = (allMoves.map (fun mv => 23 * h mv + 1)).sum := hsum
        _ = 23 * (allMoves.map h).sum + allMoves.length :=
          sum_map_mul_add_one allMoves h
        _ = 23 * (1 + (allMoves.map h).sum) + 1 := by
          rw [allMoves_length]
          omega

def r4Remaining : List (List Move × PartialMachine) := residuals r4Subtree

theorem r4Subtree_expandedNodes : expandedNodes r4Subtree = 7 := by
  decide

theorem r4Subtree_closedLeaves : closedLeaves r4Subtree = 1 := by
  decide

theorem r4Remaining_count : r4Remaining.length = 161 := by
  have h := residuals_closed_expanded r4Subtree
  rw [r4Subtree_expandedNodes, r4Subtree_closedLeaves] at h
  dsimp [r4Remaining]
  omega

/-- The source-checked r4 subtree covers its entire p23 parent except for
    the 161 explicit off-path residual cylinders. -/
theorem r4Remaining_sound :
    ∀ m, compatible p23 m →
      WeightedBound 7014 m ∨
        ∃ e ∈ r4Remaining, compatible e.2 m := by
  intro m hm
  rcases RootedFrontier.sound r4Subtree m hm with hbound |
    ⟨address,q,hopen,hcompat⟩
  · exact Or.inl hbound
  · exact Or.inr ⟨(address,q), by
      simpa [r4Remaining] using OpenLeaf.mem_residuals hopen, hcompat⟩

/-- The actual p23 address/table pair is one entry of the accepted canonical
    77; this is the membership needed for a sound roster graft. -/
theorem p23_parent_count :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter
      (fun e => sameTable e.2 p23)).length = 1 := by
  decide

noncomputable def r4RefinedRoster : List (List Move × PartialMachine) :=
  graftRoster p23 r4Remaining BB6.Agent47CanonicalRaw114Accepted.roster

/-- Canonical-77 soundness survives replacing precisely p23 by the r4
    first-hole frontier. The result is conditional only on the 161 residual
    Covers; the 625-completion r4 terminal cylinder is already discharged
    by the source-connected certificate in RootFrontierR1R4. -/
theorem r4RefinedRoster_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ r4RefinedRoster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound (p := p23) (replacement := r4Remaining)
    (roster := BB6.Agent47CanonicalRaw114Accepted.roster)
    (by decide) BB6.Agent47CanonicalRaw114Accepted.sound r4Remaining_sound

/-- The terminal r4 parent has exactly two remaining transition holes, hence
    the closed terminal cylinder contains 25^2 = 625 raw completions. -/
theorem r4_terminal_hole_count :
    (slots.filter (fun s => BB6.Agent47R4Parent.r4.parent s = none)).length = 2 := by
  decide

theorem r4_terminal_mass : 25 ^ 2 = 625 := by norm_num

#print axioms residuals_closed_expanded
#print axioms r4Subtree
#print axioms r4Remaining_sound
#print axioms r4RefinedRoster_sound
#print axioms r4_terminal_hole_count

end BB6.Agent50CanonicalR4Ingestion
