import ChampionF1OneLBIntegration
import HardRootLeaves
import CryptidsTapeAdapter
import WeightedNonhaltLeafAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent41Raw139CryptidsLeaf

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent8TNFPath
open BB6.Agent6ChampionResidual
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50TNFPilot
open BB6.Agent6F1OneLBIntegration

/-- Exact pinned upstream Cryptids nonhalting machine. -/
def source : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH.machine

/-- Local literal table in A0,A1,...,F1 order. -/
def candidate : Machine := BB6.Agent19HardRoot.literal [
  some ⟨true,true,1⟩,  some ⟨false,false,4⟩,
  some ⟨true,true,2⟩,  some ⟨false,false,2⟩,
  some ⟨true,true,3⟩,  some ⟨false,true,1⟩,
  some ⟨true,false,0⟩, some ⟨false,false,4⟩,
  some ⟨true,false,3⟩, some ⟨true,false,5⟩,
  some ⟨true,false,3⟩, none
]

def original : Machine := BB6.ConjectureBridge.toAgent8 source

theorem original_eq_candidate : original = candidate := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

/-- Transfer the pinned upstream IsNotHalt theorem through the exact tape bridge. -/
theorem original_never : NeverHalts original :=
  BB6.ConjectureBridge.not_halts_to_agent8 source
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source).mp
      (by simpa [source] using
        BusyBeaver.M_1RB0LE_1RC0RC_1LD0RB_1LA0LE_1LD1LF_1LDHHH.is_not_halt))

theorem candidate_never : NeverHalts candidate := by
  rw [← original_eq_candidate]
  exact original_never

/-- Forgetting the sole F1 halt row gives the exact 25-completion leaf. -/
def candidateLeaf : PartialMachine := forgetHaltRows candidate

theorem candidate_hole :
    ∀ s, candidateLeaf s = none ↔ s = (⟨5, by decide⟩, true) := by
  decide

/-- First-use times after the initial A0 query at time zero. -/
def candidateSchedule : List (Nat × Slot) :=
  [ (1, (1,false)),
    (2, (2,false)),
    (3, (3,true)),
    (4, (4,true)),
    (5, (5,false)),
    (6, (3,false)),
    (8, (1,true)),
    (9, (2,true)),
    (25,(4,false)),
    (27,(0,true)) ]

theorem candidate_first_hole_path : FirstHolePath candidateLeaf 6 :=
  checked_from_root _ candidateSchedule (by decide)

/-- The first divergence from the champion is D1=0LE, E1=1LF. -/
def candidateMove : Move := ⟨true,false,5⟩

def candidateAddress : List Move :=
  [⟨false,false,4⟩, candidateMove]

def candidateParent : PartialMachine :=
  championChild 1 candidateMove

theorem candidateParentPath : RawRootPath candidateParent :=
  championChildPath 1 candidateMove

/-- Candidate first-hole schedule in the rooted-frontier format. -/
def candidatePathEntries : List PathEntry :=
  candidateSchedule.map fun (n,s) =>
    (n,s,(candidate s).getD ⟨false,false,0⟩)

def candidateTail : List PathEntry :=
  candidatePathEntries.drop 4

theorem candidateTail_endpoint :
    (pathEnd candidateParent 6 candidateTail).1 = candidateLeaf := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> decide

theorem candidateTail_cut :
    (pathEnd candidateParent 6 candidateTail).2 = 6 := by
  decide

theorem candidateTail_pathOK :
    pathOKB 7014 candidateParent 6 candidateTail = true := by
  decide

/-- A source-certified 25-completion leaf, expanded with all off-path siblings retained. -/
def candidateWeightedLeaf (B : Nat) :
    WeightedTNFCertificate B candidateLeaf 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [candidate, BB6.Agent19HardRoot.literal, initialSlot]
  · exact candidate_never

noncomputable def candidateFrontier :
    RootedFrontier 7014 candidateParent :=
  buildFrontierB 7014 candidateParent 6 candidateParentPath
    candidateTail candidateTail_pathOK
    (by
      rw [candidateTail_endpoint]
      exact candidateWeightedLeaf 7014)

theorem candidateFrontier_sound :
    ∀ m, compatible candidateParent m →
      WeightedBound 7014 m ∨
        ∃ address q, OpenLeaf candidateFrontier address q ∧ compatible q m :=
  RootedFrontier.sound candidateFrontier

theorem candidateOpenLeaf_mem_residuals {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    (address,q) ∈ RootedFrontier.residuals f := by
  induction h with
  | here path =>
      simp [RootedFrontier.residuals]
  | @child p n c path hrun hhole hweight children mv address q hchild ih =>
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address,q), ih, rfl⟩

noncomputable def candidateRemaining : List (List Move × PartialMachine) :=
  RootedFrontier.residuals candidateFrontier

theorem candidateRemaining_sound :
    ∀ m, compatible candidateParent m →
      WeightedBound 7014 m ∨
        ∃ e ∈ candidateRemaining, compatible e.2 m := by
  intro m hm
  rcases candidateFrontier_sound m hm with hbound | ⟨address,q,hopen,hcompat⟩
  · exact Or.inl hbound
  · exact Or.inr ⟨(address,q), candidateOpenLeaf_mem_residuals hopen, hcompat⟩

/-- The exact current 102-entry frontier contains this E1=1LF parent at address
    [D1=0LE, E1=1LF]. This is a current residual, not merely raw139-parent compatibility. -/
theorem candidateParent_current_entry :
    ∃ e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLB,
      e.1 = candidateAddress ∧ sameTable e.2 candidateParent = true := by
  decide

theorem candidateParent_current_unique :
    (remainingF1AfterZeroRBZeroLAOneRDOneLB.filter
      (fun e => sameTable e.2 candidateParent)).length = 1 := by
  decide

/-- Replace only the exact current E1=1LF residual by its source-checked
    first-hole descendants. Every other current residual is preserved. -/
noncomputable def candidateRefinedCurrent :
    List (List Move × PartialMachine) :=
  (remainingF1AfterZeroRBZeroLAOneRDOneLB.filter
    (fun e => !(sameTable e.2 candidateParent))) ++
  (candidateRemaining.map fun (address,q) => (candidateAddress ++ address,q))

theorem candidateParent_cover
    (hOpen : ∀ e ∈ candidateRefinedCurrent,
      Cover (WeightedBound championScore) e.2) :
    Cover (WeightedBound championScore) candidateParent := by
  refine Cover.leaf candidateParent ?_
  intro m hm k d hk hd
  rcases candidateRemaining_sound m hm with hbound | ⟨e, he, hcompat⟩
  · exact Nat.le_trans (hbound k d hk hd)
      (Nat.le_of_lt champion_score_gt_7014)
  · have hmem : (candidateAddress ++ e.1,e.2) ∈ candidateRefinedCurrent := by
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨e, he, rfl⟩
    exact hOpen (candidateAddress ++ e.1,e.2) hmem m hcompat k d hk hd

theorem cover_current_after_candidate
    (hOpen : ∀ e ∈ candidateRefinedCurrent,
      Cover (WeightedBound championScore) e.2)
    (e : List Move × PartialMachine)
    (he : e ∈ remainingF1AfterZeroRBZeroLAOneRDOneLB) :
    Cover (WeightedBound championScore) e.2 := by
  by_cases h : sameTable e.2 candidateParent = true
  · have heq : e.2 = candidateParent := sameTable_sound h
    rw [heq]
    exact candidateParent_cover hOpen
  · apply hOpen e
    apply List.mem_append.mpr
    left
    apply List.mem_filter.mpr
    exact ⟨he, by simp [h]⟩

/-- Conditional exact-BB6 consumer after replacing one live 102-frontier
    parent by its exact source-certified complement. -/
theorem exact_from_canonical77_and_raw139_candidate_leaf
    (hOther : ∀ e ∈ BB6.Agent47CanonicalRaw114Accepted.roster,
      e.2 ≠ championResidual → Cover (WeightedBound championScore) e.2)
    (hOpen : ∀ e ∈ candidateRefinedCurrent,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  exact_from_canonical77_and_raw139_four_sibling_leaves hOther
    (fun e he => cover_current_after_candidate hOpen e he)

#print axioms original_eq_candidate
#print axioms original_never
#print axioms candidate_never
#print axioms candidate_first_hole_path
#print axioms candidateTail_endpoint
#print axioms candidateTail_pathOK
#print axioms candidateWeightedLeaf
#print axioms candidateFrontier_sound
#print axioms candidateRemaining_sound
#print axioms candidateParent_current_entry
#print axioms candidateParent_current_unique
#print axioms exact_from_canonical77_and_raw139_candidate_leaf

end BB6.Agent41Raw139CryptidsLeaf
