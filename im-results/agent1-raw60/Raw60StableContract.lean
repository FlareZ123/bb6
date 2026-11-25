import CanonicalTwoParentGraft
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw60Contract
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

abbrev p60 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,true,0⟩)

theorem member76 :
    ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76, sameTable e.2 p60 = true := by
  have h : BB6.Agent47CanonicalTwoParent.roster76.any (fun e => sameTable e.2 p60) = true := by
    decide
  exact List.any_eq_true.mp h

theorem remainder75 :
    (BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 p60))).length = 75 := by decide

/-- A physical parent refinement is a stable local Cover at the target,
independently of quotient roster counts or other parent refinements. -/
theorem cover_of_local_partition {B C : Nat} {p : PartialMachine}
    {children : List Entry} (hCB : C ≤ B)
    (hlocal : ∀ m, compatible p m → WeightedBound C m ∨
      ∃ r ∈ children, compatible r.2 m)
    (hchildren : ∀ r ∈ children, Cover (WeightedBound B) r.2) :
    Cover (WeightedBound B) p := by
  apply Cover.leaf
  intro m hm
  rcases hlocal m hm with hb | ⟨r, hr, hrc⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hCB
  · exact (hchildren r hr).sound m hrc

/-- Any family of independently supplied parent Covers can satisfy the
stable roster's matching entries. All unmatched entries remain explicit. -/
theorem roster_covers_of_selected {B : Nat} {roster : List Entry}
    {parents : List PartialMachine}
    (hparents : ∀ p ∈ parents, Cover (WeightedBound B) p)
    (hrest : ∀ e ∈ roster.filter
      (fun e => !(parents.any (fun p => sameTable e.2 p))),
      Cover (WeightedBound B) e.2) :
    ∀ e ∈ roster, Cover (WeightedBound B) e.2 := by
  intro e he
  cases h : parents.any (fun p => sameTable e.2 p) with
  | false =>
      exact hrest e (List.mem_filter.mpr ⟨he, by simp [h]⟩)
  | true =>
      obtain ⟨p, hp, hmatch⟩ := List.any_eq_true.mp h
      rw [sameTable_sound hmatch]
      exact hparents p hp

/-- Independent contract for the Raw60 weighted parent bound. -/
theorem raw60_cover {B : Nat} (hB : 1175 ≤ B)
    (h60 : ∀ m, compatible p60 m → WeightedBound 1175 m) :
    Cover (WeightedBound B) p60 := by
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (h60 m hm k d hk hd) hB

/-- Fill just Raw60's slot in the stable 76 roster; the other Covers
remain explicit. No dependency on Raw107/Raw114 proof objects here. -/
theorem fill_raw60 {B : Nat} (hB : 1175 ≤ B)
    (h60 : ∀ m, compatible p60 m → WeightedBound 1175 m)
    (hrest : ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76.filter
      (fun e => !(sameTable e.2 p60)), Cover (WeightedBound B) e.2) :
    ∀ e ∈ BB6.Agent47CanonicalTwoParent.roster76, Cover (WeightedBound B) e.2 := by
  apply roster_covers_of_selected (parents := [p60])
  · intro p hp
    have heq : p = p60 := by simpa using hp
    rw [heq]
    exact raw60_cover hB h60
  · simpa using hrest

#print axioms member76
#print axioms remainder75
#print axioms cover_of_local_partition
#print axioms roster_covers_of_selected
#print axioms raw60_cover
#print axioms fill_raw60
end BB6.Agent1Raw60Contract
