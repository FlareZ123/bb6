import HardRootLeaves
import F287HaltFreedom
import WeightedNonhaltLeafAdapter
import FourHoleRootFrontier
import FourHoleResidualRoster
import CanonicalRosterRefinement
import CanonicalRaw114Accepted
import TNFPilot

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent48A6Ingestion

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent19HardRoot
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalRefinement
open BB6.Agent50TNFPilot

/-- The hard-root table is exactly the literal original-source F287 table. -/
theorem A6_eq_expectedRLE :
    BB6.Agent19HardRoot.A6 = BB6.F287.expectedRLE := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

/-- The pinned Cryptids source theorem discharges the exact A6 table in the
same Lean kernel as the accepted canonical-77 artifact. -/
theorem A6_never : NeverHalts BB6.Agent19HardRoot.A6 := by
  rw [A6_eq_expectedRLE]
  exact BB6.F287.literal_never

/-- The exact A6 one-hole cylinder is closed by the existing weighted
nonhalt adapter, for every score bound. -/
theorem A6_weighted_certificate (B : Nat) :
    WeightedTNFCertificate B
      (BB6.Agent47WeightedHalt.forgetHaltRows BB6.Agent19HardRoot.A6) 6 :=
  BB6.Agent47WeightedHalt.forgetHaltRows_nonhaltCertificate
    B BB6.Agent19HardRoot.A6 (by decide) A6_never

theorem A6_weighted_cover (B : Nat) :
    Cover (WeightedBound B)
      (BB6.Agent47WeightedHalt.forgetHaltRows BB6.Agent19HardRoot.A6) :=
  (A6_weighted_certificate B).toCover

/-- All completions of the certified A6 leaf remain inside its exact raw139
D1=0LC parent. -/
theorem A6_leaf_subcover (B : Nat) (m : Machine)
    (hm : compatible (BB6.Agent47WeightedHalt.forgetHaltRows
      BB6.Agent19HardRoot.A6) m) :
    WeightedBound B m ∧ compatible BB6.Agent19HardRoot.p139 m :=
  ⟨(A6_weighted_certificate B).sound m hm,
    BB6.Agent19HardRoot.A6_leaf_parent m hm⟩

abbrev PathEntry := BB6.Agent50TNFPilot.PathEntry

/-- Derive actual ordinary transitions from the A6 literal table; the
stored first-hole schedule supplies only times and slots. -/
def A6_pathEntries : List PathEntry :=
  BB6.Agent19HardRoot.A6_schedule.map fun x =>
    (x.1, x.2,
      (BB6.Agent19HardRoot.A6 x.2).getD ⟨false,false,0⟩)

def A6_tail : List PathEntry := A6_pathEntries.drop 2

/-- Convert the existing pathOK checker into the raw ancestry certificate
used by the sibling-preserving rooted frontier. -/
theorem rawRootPath_of_pathOK
    (p : PartialMachine) (cut : Nat) (xs : List PathEntry)
    (hp : RawRootPath p)
    (h : BB6.Agent50TNFPilot.pathOK p cut xs = true) :
    RawRootPath (BB6.Agent50TNFPilot.pathEnd p cut xs).1 := by
  induction xs generalizing p cut with
  | nil =>
      simpa [BB6.Agent50TNFPilot.pathEnd] using hp
  | cons entry xs ih =>
      rcases entry with ⟨n,s,mv⟩
      simp only [BB6.Agent50TNFPilot.pathOK, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rcases h with ⟨hhole,hrest⟩
      rcases hrest with ⟨hread,hrest⟩
      rcases hrest with ⟨_hslot,hrest⟩
      rcases hrest with ⟨_hmove,htail⟩
      cases hr : knownRun p n with
      | none =>
          simp [hr] at hread
      | some c =>
          have hs : readSlot c = s := by simpa [hr] using hread
          subst s
          have hpath : RawRootPath (refine p (readSlot c) (some mv)) :=
            RawRootPath.step hp hr hhole
          simpa [BB6.Agent50TNFPilot.pathEnd] using
            ih (refine p (readSlot c) (some mv))
              (BB6.Agent8TNFPath.advanceCut cut mv) hpath htail

/-- The accepted raw139 parent is exactly the first two transitions of A6's
original first-hole schedule. -/
theorem p139_rawRootPath : RawRootPath BB6.Agent19HardRoot.p139 := by
  have hprefix :
      BB6.Agent50TNFPilot.pathOK BB6.Agent50TNFPilot.root 2
        (A6_pathEntries.take 2) = true := by decide
  have h := rawRootPath_of_pathOK BB6.Agent50TNFPilot.root 2
    (A6_pathEntries.take 2) RawRootPath.root hprefix
  simpa [BB6.Agent19HardRoot.p139, BB6.Agent19HardRoot.root,
    A6_pathEntries, BB6.Agent19HardRoot.A6_schedule,
    BB6.Agent19HardRoot.A6, BB6.Agent19HardRoot.literal,
    BB6.Agent50TNFPilot.pathEnd, BB6.Agent50TNFPilot.root] using h

/-- The remaining eight first-hole decisions terminate at the exact
forget-halt-row A6 leaf, with cut six. -/
theorem A6_tail_endpoint :
    (BB6.Agent50TNFPilot.pathEnd BB6.Agent19HardRoot.p139 4 A6_tail).1 =
      BB6.Agent47WeightedHalt.forgetHaltRows BB6.Agent19HardRoot.A6 := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> decide

theorem A6_tail_cut :
    (BB6.Agent50TNFPilot.pathEnd BB6.Agent19HardRoot.p139 4 A6_tail).2 = 6 := by
  decide

/-- Every halt sibling along the eight-edge path is already below the
accepted canonical-77 bound 7014. -/
theorem A6_tail_pathOK :
    BB6.Agent31FourHoleFrontier.pathOKB 7014
      BB6.Agent19HardRoot.p139 4 A6_tail = true := by
  decide

/-- Expand raw139 along A6's checked path. Every off-path ordinary sibling
remains an explicit open leaf; halt siblings are bounded, and the terminal
25-completion A6 leaf is closed by its source theorem. -/
def A6_frontier :
    BB6.Agent31FourHoleFrontier.RootedFrontier 7014
      BB6.Agent19HardRoot.p139 :=
  BB6.Agent31FourHoleFrontier.buildFrontierB 7014
    BB6.Agent19HardRoot.p139 4 p139_rawRootPath A6_tail A6_tail_pathOK
    (by
      rw [A6_tail_endpoint]
      exact A6_weighted_certificate 7014)

theorem A6_frontier_sound :
    ∀ m, compatible BB6.Agent19HardRoot.p139 m →
      WeightedBound 7014 m ∨
        ∃ address q, OpenLeaf A6_frontier address q ∧ compatible q m :=
  BB6.Agent31FourHoleFrontier.RootedFrontier.sound A6_frontier

theorem openLeaf_mem_residuals {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    (address,q) ∈ BB6.Agent31FourHoleFrontier.residuals f := by
  induction h with
  | here path =>
      simp [BB6.Agent31FourHoleFrontier.residuals]
  | @child p n c path hrun hhole hweight children mv address q hchild ih =>
      apply List.mem_flatMap.mpr
      refine ⟨mv, BB6.Agent31FourHoleFrontier.allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address,q), ih, rfl⟩

def A6_remaining : List (List Move × PartialMachine) :=
  BB6.Agent31FourHoleFrontier.residuals A6_frontier

/-!
The residual-list cardinalities are intentionally proved in a separate
structural count module. A giant executable `decide` reduction here triggers
a Lean 4.36.0-rc2 IR compiler panic; neither count is needed for the soundness
theorems below.
-/

/-- Exact local partial cover: only off-path ordinary siblings remain open;
no unresolved sibling is silently discarded. -/
theorem A6_remaining_sound :
    ∀ m, compatible BB6.Agent19HardRoot.p139 m →
      WeightedBound 7014 m ∨
        ∃ e ∈ A6_remaining, compatible e.2 m := by
  intro m hm
  rcases A6_frontier_sound m hm with hbound | ⟨address,q,hopen,hcompat⟩
  · exact Or.inl hbound
  · exact Or.inr ⟨(address,q), openLeaf_mem_residuals hopen, hcompat⟩

/-- Replace exactly the raw139 entry in the accepted canonical-77 roster by
its explicit unresolved descendants. All other roster entries remain. -/
noncomputable def A6_refinedRoster :
    List (List Move × PartialMachine) :=
  BB6.Agent47CanonicalRefinement.graftRoster
    BB6.Agent19HardRoot.p139 A6_remaining
    BB6.Agent47CanonicalRaw114Accepted.roster

theorem p139_parent_count :
    (BB6.Agent47CanonicalRaw114Accepted.roster.filter
      (fun e => BB6.Agent31FourHoleRoster.sameTable e.2
        BB6.Agent19HardRoot.p139)).length = 1 := by decide

/- The 260-entry cardinality is deferred with A6_remaining_count. -/

/-- The source-connected A6 refinement preserves the global 7014-bound
dichotomy and every unresolved sibling in the other 76 canonical parents. -/
theorem A6_refinedRoster_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound 7014 m ∨
        ∃ e ∈ A6_refinedRoster, TNFQuotientCompatible e.2 m := by
  simpa [A6_refinedRoster] using
    (BB6.Agent47CanonicalRefinement.graftRoster_sound
      (p := BB6.Agent19HardRoot.p139)
      (replacement := A6_remaining)
      (roster := BB6.Agent47CanonicalRaw114Accepted.roster)
      (by decide)
      BB6.Agent47CanonicalRaw114Accepted.sound
      A6_remaining_sound)

#print axioms A6_eq_expectedRLE
#print axioms A6_never
#print axioms A6_weighted_certificate
#print axioms A6_frontier_sound
#print axioms A6_remaining_sound
#print axioms A6_refinedRoster_sound

end BB6.Agent48A6Ingestion
