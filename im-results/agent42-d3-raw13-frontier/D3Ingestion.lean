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

/-- D3's score is unknown. A terminal certificate must be supplied at the
    actual target bound. The five halt siblings can be discharged at that bound
    if the path checker is supplied. -/
noncomputable def D3_frontier (B : Nat)
    (hpath : BB6.Agent31FourHoleFrontier.pathOKB B
      d3ResidualEntry.2 4 D3_tail = true)
    (hD3 : Cover (WeightedBound B) d3Leaf) :
    RootedFrontier B d3ResidualEntry.2 :=
  buildFrontierB B d3ResidualEntry.2 4 D3_parent_rawRootPath
    D3_tail hpath
    (by
      rw [D3_tail_endpoint]
      exact WeightedTNFCertificate.ofWeightedCover
        (forgetHaltRows_root D3 (by decide))
        (forgetHaltRows_tnfSupport D3)
        (forgetHaltRows_noAssignedHalt D3) hD3)

theorem D3_frontier_sound (B : Nat)
    (hpath : BB6.Agent31FourHoleFrontier.pathOKB B
      d3ResidualEntry.2 4 D3_tail = true)
    (hD3 : Cover (WeightedBound B) d3Leaf) :
    ∀ m, compatible d3ResidualEntry.2 m →
      WeightedBound B m ∨
        ∃ address q, OpenLeaf (D3_frontier B hpath hD3) address q ∧ compatible q m :=
  RootedFrontier.sound (D3_frontier B hpath hD3)

#print axioms D3_parent_rawRootPath
#print axioms D3_tail_endpoint
#print axioms D3_frontier_sound

end BB6.Agent42D3Ingestion
