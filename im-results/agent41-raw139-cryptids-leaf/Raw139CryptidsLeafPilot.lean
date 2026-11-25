import ChampionResidualParentIntegration
import CanonicalTwoParentRosterOnly
import CanonicalRosterRefinement
import CanonicalFrontier
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
open BB6.Agent31ChampionParentIntegration
open BB6.Agent47CanonicalRefinement
open BB6.Agent47CanonicalFrontier
open BB6.Agent47CanonicalTwoParent
open BB6.Agent31CanonicalTwoParentRosterOnly

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

/-- The first divergence from the champion path is D1=0LE, E1=1LF. -/
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
    pathOKB championScore candidateParent 6 candidateTail = true := by
  decide

/-- The source theorem closes every completion of the one-row F1 leaf. -/
def candidateWeightedLeaf (B : Nat) :
    WeightedTNFCertificate B candidateLeaf 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [candidate, BB6.Agent19HardRoot.literal, initialSlot]
  · exact candidate_never

/-- Refine only the exact E1=1LF parent, keeping every off-path sibling open. -/
noncomputable def candidateFrontier :
    RootedFrontier championScore candidateParent :=
  buildFrontierB championScore candidateParent 6 candidateParentPath
    candidateTail candidateTail_pathOK
    (by
      rw [candidateTail_endpoint]
      exact candidateWeightedLeaf championScore)

theorem candidateFrontier_sound :
    ∀ m, compatible candidateParent m →
      WeightedBound championScore m ∨
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
      change (mv :: address,q) ∈
        RootedFrontier.residuals (.expand path hrun hhole hweight children)
      simp only [RootedFrontier.residuals]
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address,q), ih, rfl⟩

noncomputable def candidateRemaining : List (List Move × PartialMachine) :=
  RootedFrontier.residuals candidateFrontier

theorem candidateRemaining_sound :
    ∀ m, compatible candidateParent m →
      WeightedBound championScore m ∨
        ∃ e ∈ candidateRemaining, compatible e.2 m := by
  intro m hm
  rcases candidateFrontier_sound m hm with hbound | ⟨address,q,hopen,hcompat⟩
  · exact Or.inl hbound
  · exact Or.inr ⟨(address,q), candidateOpenLeaf_mem_residuals hopen, hcompat⟩

/-- The candidate parent is an exact open leaf of the current 123-leaf
    champion-containing raw139 frontier, not merely a compatible ancestor. -/
theorem candidateParent_current_entry :
    ∃ e ∈ championResidualFrontierWithParentResiduals,
      e.1 = candidateAddress ∧ sameTable e.2 candidateParent = true := by
  decide

theorem candidateParent_current_address_unique :
    ∀ e ∈ championResidualFrontierWithParentResiduals,
      sameTable e.2 candidateParent = true →
      e.1 = candidateAddress ∧ e.2 = candidateParent := by
  decide

/-- Replace just that open leaf by its exact rooted descendants. The other
    122 raw139 residuals are retained unchanged. -/
noncomputable def raw139ResidualsWithCandidate :
    List (List Move × PartialMachine) :=
  (championResidualFrontierWithParentResiduals.filter
    (fun e => !(sameTable e.2 candidateParent))) ++
  (candidateRemaining.map fun (address,q) => (candidateAddress ++ address,q))

/-- Stable local parent contract: the complete raw139 cylinder is either
    already bounded or represented by the explicitly refined residuals. -/
theorem raw139_parent_contract :
    ∀ m, compatible championResidual m →
      WeightedBound championScore m ∨
        ∃ e ∈ raw139ResidualsWithCandidate, compatible e.2 m := by
  intro m hm
  rcases championResidualFrontierWithParentSound m hm with hbound | ⟨address,q,hopen,hcompat⟩
  · exact Or.inl hbound
  · by_cases hmatch : sameTable q candidateParent = true
    · have hq : q = candidateParent := sameTable_sound hmatch
      subst q
      have haddr : address = candidateAddress :=
        (candidateParent_current_address_unique
          (address,candidateParent) (openLeaf_mem_residuals hopen) hmatch).1
      subst address
      rcases candidateRemaining_sound m hcompat with hbound | ⟨e,he,hc⟩
      · exact Or.inl hbound
      · exact Or.inr ⟨(candidateAddress ++ e.1,e.2), by
          apply List.mem_append.mpr
          right
          apply List.mem_map.mpr
          exact ⟨e,he,rfl⟩, hc⟩
    · exact Or.inr ⟨(address,q), by
        apply List.mem_append.mpr
        left
        apply List.mem_filter.mpr
        exact ⟨openLeaf_mem_residuals hopen, by simp [hmatch]⟩, hcompat⟩

/-- The raw139 representative survives the accepted two-parent 76-way roster. -/
theorem championResidual_mem_roster76 :
    ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
      e.1 = championResidualAddress ∧ sameTable e.2 championResidual = true := by
  decide

theorem canonical76_root_sound_at_champion :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound championScore m ∨
        ∃ e ∈ BB6.Agent47CanonicalTwoParent.roster76,
          TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases BB6.Agent31CanonicalTwoParentRosterOnly.roster76_sound m hm with hbound | hres
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hbound k d hk hd)
        (Nat.le_of_lt BB6.Agent31Canonical78Exact.champion_score_gt_7014))
  · exact Or.inr hres

/-- Generic quotient-roster graft: replace raw139 by the refined local
    residuals without creating a parallel count-specific roster system. -/
noncomputable def canonical76WithRaw139Candidate :
    List (List Move × PartialMachine) :=
  BB6.Agent47CanonicalRefinement.graftRoster
    championResidual raw139ResidualsWithCandidate
    BB6.Agent47CanonicalTwoParent.roster76

theorem canonical76WithRaw139Candidate_sound :
    ∀ m, compatible BB6.Agent50TNFPilot.root m →
      WeightedBound championScore m ∨
        ∃ e ∈ canonical76WithRaw139Candidate,
          TNFQuotientCompatible e.2 m :=
  BB6.Agent47CanonicalRefinement.graftRoster_sound
    (B := championScore)
    (root := BB6.Agent50TNFPilot.root)
    (p := championResidual)
    (replacement := raw139ResidualsWithCandidate)
    (roster := BB6.Agent47CanonicalTwoParent.roster76)
    (by decide)
    canonical76_root_sound_at_champion
    raw139_parent_contract

/-- Conditional exact-BB6 consumer through the accepted 76-way quotient
    roster. The remaining obligations are exactly the covers of the grafted
    roster entries. -/
theorem exact_from_canonical76_and_raw139_candidate_leaf
    (hLeaves : ∀ e ∈ canonical76WithRaw139Candidate,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent47CanonicalFrontier.exact_from_quotient_roster
    (C := championScore) (B := championScore)
    (by decide) (Nat.le_refl _)
    canonical76WithRaw139Candidate_sound
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

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
#print axioms candidateParent_current_address_unique
#print axioms raw139_parent_contract
#print axioms championResidual_mem_roster76
#print axioms canonical76_root_sound_at_champion
#print axioms canonical76WithRaw139Candidate_sound
#print axioms exact_from_canonical76_and_raw139_candidate_leaf

end BB6.Agent41Raw139CryptidsLeaf
