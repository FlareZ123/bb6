import Agent46Raw13Ingest77
import HardRootD3Bound
import RootedFrontierCount
import GraftRosterCount

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42D3Ingestion

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent19HardRoot
open BB6.Agent31FourHoleFrontier
open BB6.Agent47WeightedHalt
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement
open BB6.Agent50TNFPilot
open BB6.Agent42FrontierCount
open BB6.Agent46Raw13
open BB6.Agent46Raw13Canonical77

abbrev PathEntry := BB6.Agent50TNFPilot.PathEntry

/-- Attach the literal D3 moves to the checked first-hole schedule. -/
def D3_pathEntries : List PathEntry :=
  D3_schedule.map fun x =>
    (x.1, x.2, (D3 x.2).getD ⟨false,false,0⟩)

/-- The first five decisions reach the unique raw13 residual identified
    independently by Agent46's 1,716-child cut. -/
def D3_prefix : List PathEntry := D3_pathEntries.take 5

/-- The remaining five first-hole decisions reach the erased-halt D3 leaf. -/
def D3_tail : List PathEntry := D3_pathEntries.drop 5

theorem D3_prefix_pathOK :
    BB6.Agent50TNFPilot.pathOK BB6.Agent50TNFPilot.root 2 D3_prefix = true := by
  decide

theorem D3_parent_eq :
    (BB6.Agent50TNFPilot.pathEnd BB6.Agent50TNFPilot.root 2 D3_prefix).1 =
      d3ResidualEntry.2 := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> decide

theorem D3_parent_cut :
    (BB6.Agent50TNFPilot.pathEnd BB6.Agent50TNFPilot.root 2 D3_prefix).2 = 4 := by
  decide

/-- The raw13 descendant has an actual first-hole ancestry path from the
    original first-one cylinder, not merely a table-compatibility claim. -/
theorem D3_parent_rawRootPath : RawRootPath d3ResidualEntry.2 := by
  have h := rawRootPath_of_pathOK
    BB6.Agent50TNFPilot.root 2 D3_prefix RawRootPath.root D3_prefix_pathOK
  rw [D3_parent_eq] at h
  exact h

theorem pathEnd_append (p : PartialMachine) (cut : Nat)
    (xs ys : List PathEntry) :
    BB6.Agent50TNFPilot.pathEnd p cut (xs ++ ys) =
      BB6.Agent50TNFPilot.pathEnd
        (BB6.Agent50TNFPilot.pathEnd p cut xs).1
        (BB6.Agent50TNFPilot.pathEnd p cut xs).2 ys := by
  induction xs generalizing p cut with
  | nil => rfl
  | cons entry xs ih =>
      rcases entry with ⟨n,s,mv⟩
      simp [BB6.Agent50TNFPilot.pathEnd, ih]

theorem D3_prefix_append_tail :
    D3_prefix ++ D3_tail = D3_pathEntries := by
  simp [D3_prefix,D3_tail]

theorem D3_full_endpoint :
    BB6.Agent50TNFPilot.pathEnd BB6.Agent50TNFPilot.root 2 D3_pathEntries =
      (d3Leaf,6) := by
  apply Prod.ext
  · funext s
    rcases s with ⟨q,b⟩
    fin_cases q <;> cases b <;> decide
  · decide

/-- Exact endpoint of the five remaining ordinary transitions. -/
theorem D3_tail_endpoint :
    BB6.Agent50TNFPilot.pathEnd d3ResidualEntry.2 4 D3_tail =
      (d3Leaf,6) := by
  calc
    BB6.Agent50TNFPilot.pathEnd d3ResidualEntry.2 4 D3_tail =
        BB6.Agent50TNFPilot.pathEnd
          (BB6.Agent50TNFPilot.pathEnd BB6.Agent50TNFPilot.root 2 D3_prefix).1
          (BB6.Agent50TNFPilot.pathEnd BB6.Agent50TNFPilot.root 2 D3_prefix).2
          D3_tail := by
            rw [← D3_parent_eq, ← D3_parent_cut]
    _ = BB6.Agent50TNFPilot.pathEnd
          BB6.Agent50TNFPilot.root 2 (D3_prefix ++ D3_tail) := by
            rw [pathEnd_append]
    _ = BB6.Agent50TNFPilot.pathEnd
          BB6.Agent50TNFPilot.root 2 D3_pathEntries := by
            rw [D3_prefix_append_tail]
    _ = (d3Leaf,6) := D3_full_endpoint

/-- The five halt siblings on the D3 route all fit the canonical-77 bound. -/
theorem D3_tail_pathOK :
    BB6.Agent31FourHoleFrontier.pathOKB 21269
      d3ResidualEntry.2 4 D3_tail = true := by
  rw [← D3_parent_eq, ← D3_parent_cut]
  decide

/-- Lift the already-proved exact score-24 D3 leaf to the global 21269
    threshold. No new simulation or halt claim is introduced here. -/
theorem d3Leaf_cover21269 :
    Cover (WeightedBound 21269) d3Leaf := by
  intro m hm k d hk hd
  have h := d3Leaf_weightedBound m hm k d hk hd
  omega

/-- A certificate suitable for the existing sibling-preserving frontier
    builder, obtained from the source-checked D3 weighted cover. -/
noncomputable def d3Leaf_certificate :
    WeightedTNFCertificate 21269 d3Leaf 6 :=
  WeightedTNFCertificate.ofWeightedCover
    (forgetHaltRows_root D3 (by decide))
    (forgetHaltRows_tnfSupport D3)
    (forgetHaltRows_noAssignedHalt D3)
    d3Leaf_cover21269

/-- Refine only the unique raw13 descendant along D3's remaining five
    first-hole decisions. Halt siblings are bounded; ordinary siblings stay
    as explicit residual leaves. -/
noncomputable def D3_frontier :
    RootedFrontier 21269 d3ResidualEntry.2 :=
  buildFrontierB 21269 d3ResidualEntry.2 4 D3_parent_rawRootPath
    D3_tail D3_tail_pathOK
    (by rw [D3_tail_endpoint]; exact d3Leaf_certificate)

theorem D3_frontier_sound :
    ∀ m, compatible d3ResidualEntry.2 m →
      WeightedBound 21269 m ∨
        ∃ address q, OpenLeaf D3_frontier address q ∧ compatible q m :=
  RootedFrontier.sound D3_frontier

def D3_remaining : List (List Move × PartialMachine) :=
  residuals D3_frontier

theorem D3_remaining_count : D3_remaining.length = 115 := by
  unfold D3_remaining D3_frontier
  rw [residuals_length_buildFrontierB 21269 d3ResidualEntry.2 4
    D3_parent_rawRootPath D3_tail D3_tail_pathOK
    (by rw [D3_tail_endpoint]; exact d3Leaf_certificate)]
  have htail : D3_tail.length = 5 := by decide
  rw [htail]
  norm_num

/-- Exact local cover: every completion of this raw13 residual is either
    below the bound or lies in one of the 115 retained ordinary siblings. -/
theorem D3_remaining_sound :
    ∀ m, compatible d3ResidualEntry.2 m →
      WeightedBound 21269 m ∨
        ∃ e ∈ D3_remaining, compatible e.2 m := by
  intro m hm
  rcases D3_frontier_sound m hm with hbound | ⟨address,q,hopen,hcompat⟩
  · exact Or.inl hbound
  · exact Or.inr ⟨(address,q), OpenLeaf_mem_residuals hopen, hcompat⟩

/-- Replace exactly the D3 descendant in the already accepted 1,792-entry
    canonical-77 roster. The original other 1,791 entries are preserved. -/
noncomputable def D3_refinedRoster77 : List (List Move × PartialMachine) :=
  graftRoster d3ResidualEntry.2 D3_remaining refinedRoster77

theorem D3_parent_count77 :
    (refinedRoster77.filter
      (fun e => sameTable e.2 d3ResidualEntry.2)).length = 1 := by
  decide

theorem D3_refinedRoster_sound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound 21269 m ∨
      ∃ e ∈ D3_refinedRoster77, TNFQuotientCompatible e.2 m := by
  simpa [D3_refinedRoster77] using
    (graftRoster_sound
      (p := d3ResidualEntry.2)
      (replacement := D3_remaining)
      (roster := refinedRoster77)
      (by decide)
      refined_sound77
      D3_remaining_sound) m hm

theorem D3_refinedRoster_count :
    D3_refinedRoster77.length = 1906 := by
  have h := graftRoster_length_of_one d3ResidualEntry.2
    D3_remaining refinedRoster77 (by
      simpa [graftMatchCount] using D3_parent_count77)
  change D3_refinedRoster77.length + 1 =
    refinedRoster77.length + D3_remaining.length at h
  rw [refined_count77, residual_count, D3_remaining_count] at h
  omega

/-- Conditional global cover after all retained residuals are discharged. -/
theorem cover_at_target_D3 (B : Nat) (hB : 21269 ≤ B)
    (hLeaves : ∀ e ∈ D3_refinedRoster77, Cover (WeightedBound B) e.2) :
    Cover (WeightedBound B) BB6.CoverageAdapter.firstOneCylinder :=
  cover_of_quotient_roster hB D3_refinedRoster_sound hLeaves

/-- Conditional exactness interface after the D3 frontier graft. -/
theorem exact_at_target_D3 (B : Nat) (hB : 21269 ≤ B)
    (hLeaves : ∀ e ∈ D3_refinedRoster77, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB D3_refinedRoster_sound hLeaves champ

#print axioms D3_parent_rawRootPath
#print axioms D3_tail_endpoint
#print axioms d3Leaf_cover21269
#print axioms D3_frontier_sound
#print axioms D3_remaining_sound
#print axioms D3_refinedRoster_sound
#print axioms D3_refinedRoster_count
#print axioms cover_at_target_D3
#print axioms exact_at_target_D3

end BB6.Agent42D3Ingestion
