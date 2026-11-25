import FourHoleRootFrontier
import Raw120CanonicalPartition

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120FourHoleIngestion

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent3Raw120
open BB6.Agent3Raw120Partition

/-- The residual-list view of a rooted frontier is exactly its OpenLeaf
    relation. This lets the raw120 table be identified in the independently
    checked four-hole rooted frontier without comparing informal JSON. -/
theorem mem_residuals_iff {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) (address : List Move) (q : PartialMachine) :
    (address, q) ∈ residuals f ↔ OpenLeaf f address q := by
  induction f with
  | residual path =>
      simp [residuals]
  | closed path cert =>
      simp [residuals]
  | @expand p n c path hrun hhole hweight children ih =>
      simp only [residuals, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨mv, hmv, a, ha, hEq⟩
        rcases Prod.mk.inj hEq with ⟨haddr, hq⟩
        subst address
        subst q
        exact OpenLeaf.child path hrun hhole hweight children mv ((ih mv).mp ha)
      · intro h
        cases h with
        | child path hrun hhole hweight children mv hchild =>
            exact ⟨mv, allMoves_complete mv, (address, q), (ih mv).mpr hchild, rfl⟩

/-- The exact p120 partial machine is an off-path residual of the
    seven-edge first-one frontier, at address 1RC/0RD/1LD/1RE/1LE. -/
theorem p120_mem_rootFrontier :
    (raw120Address, p120) ∈ residuals rootFrontier := by
  decide

theorem p120_open_leaf :
    OpenLeaf rootFrontier raw120Address p120 :=
  (mem_residuals_iff rootFrontier raw120Address p120).mp p120_mem_rootFrontier

/-- The residual is unique at this address: two distinct open leaves cannot
    both admit the same concrete completion. -/
theorem p120_leaf_unique_address {address : List Move}
    (h : OpenLeaf rootFrontier address p120) :
    address = raw120Address := by
  by_contra hne
  have hpair : (address, p120) ≠ (raw120Address, p120) := by
    intro heq
    exact hne (congrArg Prod.fst heq)
  have hdis := rootFrontier_openLeaves_disjoint
    address p120 raw120Address p120 h p120_open_leaf hpair lateMachine
  exact hdis ⟨late_compatible_raw120, late_compatible_raw120⟩

theorem weightedBound_mono {A B : Nat} {m : Machine}
    (hAB : A ≤ B) (hA : WeightedBound A m) :
    WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (hA k d hk hd) hAB

/-- Cross-route ingestion: the source-accepted four-hole root frontier is
    refined at its exact p120 residual by the weighted first-hole partition.
    The halt, 0RF and 0RB cylinders are discharged; every other root residual
    and all 22 uncovered p120 children remain explicit. -/
theorem rootFrontier_raw120_ingestion (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 18859 m ∨
      (∃ address q, OpenLeaf rootFrontier address q ∧
        q ≠ p120 ∧ compatible q m) ∨
      (∃ t, t ∈ remaining ∧ compatible (refine p120 hole t) m) := by
  rcases rootFrontier_sound m hm with hBound | ⟨address, q, hOpen, hq⟩
  · exact Or.inl (weightedBound_mono (by omega) hBound)
  · by_cases hq120 : q = p120
    · subst q
      have hAddress : address = raw120Address :=
        p120_leaf_unique_address hOpen
      subst address
      rcases partition_sound 18859 (by omega) m hq with hBound | ⟨t, ht, hchild⟩
      · exact Or.inl hBound
      · exact Or.inr (Or.inr ⟨t, ht, hchild⟩)
    · exact Or.inr (Or.inl ⟨address, q, hOpen, hq120, hq⟩)

theorem retained_child_count : remaining.length = 22 :=
  remaining_count

theorem retained_child_mass : remaining_mass = 22 * 25^5 :=
  remaining_mass

theorem p120_first_hole_mass :
    25^6 = 3 * 25^5 + 22 * 25^5 := by
  norm_num

#print axioms p120_open_leaf
#print axioms p120_leaf_unique_address
#print axioms rootFrontier_raw120_ingestion

end BB6.Agent3Raw120FourHoleIngestion
