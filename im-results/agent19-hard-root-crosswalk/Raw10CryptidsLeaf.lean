import Raw10HardRootR1Adapter
import CryptidsTapeAdapter
import WeightedNonhaltLeafAdapter
import BusyBeaver.Bridge
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE
import HardRootLeaves

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw10CryptidsLeaf

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent47WeightedHalt
open BB6.Agent49Box
open BB6.Agent49BoxBridge
open BB6.Agent13CrossRouteHeldLeaf109
open BB6.Agent17Raw10CombinedConsumer
open BB6.Agent8TNFPath

/-- The exact pinned upstream Cryptids machine selected by the raw10 crosswalk. -/
def source : ConjectureMachines.Machine 6 2 :=
  BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE.machine

/-- Its independent literal local table, in A0,A1,...,F1 order. -/
def candidate : Machine := literal [
  some ⟨true,true,1⟩,  some ⟨false,false,2⟩,
  some ⟨true,false,2⟩, some ⟨false,true,4⟩,
  some ⟨true,false,0⟩, some ⟨true,false,3⟩,
  some ⟨true,false,0⟩, some ⟨true,false,1⟩,
  some ⟨false,true,5⟩, some ⟨true,true,0⟩,
  none,                some ⟨false,true,4⟩
]

def original : Machine := BB6.ConjectureBridge.toAgent8 source

theorem original_eq_candidate : original = candidate := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

/-- The source theorem is transferred through the existing exact tape adapter. -/
theorem original_never : NeverHalts original :=
  BB6.ConjectureBridge.not_halts_to_agent8 source
    ((ConjectureMachines.isNotHalt_toBB_iff_not_halts source).mp
      (by simpa [source] using
        BusyBeaver.M_1RB0LC_1LC0RE_1LA1LD_1LA1LB_0RF1RA_HHH0RE.is_not_halt))

theorem candidate_never : NeverHalts candidate := by
  rw [← original_eq_candidate]
  exact original_never

/-- Erasing the sole F0 halt row gives the exact 25-completion last-hole leaf. -/
def candidateLeaf : PartialMachine := forgetHaltRows candidate

theorem candidate_hole :
    ∀ s, candidateLeaf s = none ↔ s = (⟨5, by decide⟩, false) := by
  decide

/-- First-use trace after the initial A0 query at time zero.
    The eleven ordinary slots are all visited by time 20; F0 is not visited. -/
def candidateSchedule : List (Nat × Slot) :=
  [ (1, (1,false)),
    (2, (2,true)),
    (3, (3,false)),
    (5, (1,true)),
    (6, (4,true)),
    (7, (0,true)),
    (11,(2,false)),
    (14,(4,false)),
    (15,(5,true)),
    (20,(3,true)) ]

theorem candidate_first_hole_path : FirstHolePath candidateLeaf 6 :=
  checked_from_root _ candidateSchedule (by decide)

/-- Reuse the established weighted last-hole/forgetHaltRows adapter. -/
def candidateWeightedLeaf (B : Nat) :
    WeightedTNFCertificate B candidateLeaf 6 := by
  apply forgetHaltRows_nonhaltCertificate
  · simp [candidate, initialSlot]
  · exact candidate_never

theorem candidateLeafCover (B : Nat) :
    Cover (WeightedBound B) candidateLeaf :=
  Cover.leaf candidateLeaf (WeightedTNFCertificate.sound (candidateWeightedLeaf B))

/-- The entire candidate leaf is contained in residual rectangle 0 of the
    exact 41-box raw10 complement after the existing 68 certificates. -/
def candidateBox0 : Box Slot Transition :=
  List.get raw10RemainderWithCycleAndHalt ⟨0, by decide⟩

theorem candidateBox0_mem :
    candidateBox0 ∈ raw10RemainderWithCycleAndHalt := by
  simp [candidateBox0]

theorem candidateLeaf_box0_contains :
    BB6.Agent50Raw10HardRootR1Adapter.boxContainsPartial
      candidateBox0 candidateLeaf = true := by
  decide

theorem candidateLeaf_fits_box0 :
    ∀ m, compatible candidateLeaf m → Fits candidateBox0 m :=
  BB6.Agent50Raw10HardRootR1Adapter.boxContainsPartial_sound
    candidateLeaf_box0_contains

theorem candidateLeaf_parent (m : Machine)
    (hm : compatible candidateLeaf m) :
    compatible firstOneB0_1LC m := by
  have hres := (raw10RemainderWithCycleAndHalt_exact m).mp
    ⟨candidateBox0, candidateBox0_mem, candidateLeaf_fits_box0 m hm⟩
  exact hres.1

/-- The exact new certificate list: the prior 68 cylinders plus this leaf. -/
def certifiedTablesWithCandidate : List PartialMachine :=
  certifiedTablesWithCycleAndHalt ++ [candidateLeaf]

/-- Exact residual complement after consuming the new 25-machine leaf. -/
def raw10RemainderWithCandidate : List (Box Slot Transition) :=
  remainder firstOneB0_1LC certifiedTablesWithCandidate

theorem raw10RemainderWithCandidate_exact (m : Machine) :
    (∃ r ∈ raw10RemainderWithCandidate, Fits r m) ↔
      compatible firstOneB0_1LC m ∧
      (∀ w ∈ b0_1lcSideWitnesses,
        ¬ compatible (unpackTable w.table) m) ∧
      ¬ compatible held m ∧
      ¬ compatible table m ∧
      ¬ compatible haltTable m ∧
      ¬ compatible candidateLeaf m := by
  rw [raw10RemainderWithCandidate, remainder_exact]
  simp only [certifiedTablesWithCandidate, certifiedTablesWithCycleAndHalt,
    List.mem_append, sideTables, List.mem_map, List.mem_cons, List.mem_singleton]
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨hp, ?_, ?_, ?_, ?_, ?_⟩
    · intro w hw
      exact hn _ (Or.inl ⟨w, hw, rfl⟩)
    · exact hn held (Or.inr (Or.inl rfl))
    · exact hn table (Or.inr (Or.inr (Or.inl rfl)))
    · exact hn haltTable (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hn candidateLeaf (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · rintro ⟨hp, hs, hh, hc, hhalt, hcandidate⟩
    refine ⟨hp, ?_⟩
    intro q hq
    rcases hq with hside | htail
    · obtain ⟨w, hw, rfl⟩ := hside
      exact hs w hw
    · rcases htail with hHeldMem | htail
      · have he : q = held := by simpa using hHeldMem
        subst q
        exact hh
      · rcases htail with hCycleMem | htail
        · have he : q = table := by simpa using hCycleMem
          subst q
          exact hc
        · rcases htail with hHaltMem | htail
          · have he : q = haltTable := by simpa using hHaltMem
            subst q
            exact hhalt
          · have he : q = candidateLeaf := by
              simpa using List.mem_singleton.mp htail
            subst q
            exact hcandidate

theorem raw10RemainderWithCandidate_disjoint :
    raw10RemainderWithCandidate.Pairwise Disjoint :=
  remainder_disjoint _ _

/-- Exact finite count after replacing box 0 by its nine first-mismatch pieces. -/
theorem raw10RemainderWithCandidate_count :
    raw10RemainderWithCandidate.length = 49 := by
  decide

private def boxMass (b : Box Slot Transition) : Nat :=
  (slots.map fun s => (b s).length).prod

theorem raw10RemainderWithCandidate_mass :
    (raw10RemainderWithCandidate.map boxMass).sum = 90737503713700 := by
  decide

/-- A score-B consumer with exactly one additional source-certified leaf.
    The other 48 residual rectangles remain explicit obligations. -/
theorem raw10CoverWithCandidate (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCandidate,
      ∀ m, Fits r m → WeightedBound B m) :
    Cover (WeightedBound B) firstOneB0_1LC :=
  coverFromRemainder B firstOneB0_1LC certifiedTablesWithCandidate
    (fun q hq m hm => by
      rcases List.mem_append.mp hq with hs | htail
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hs
        have hb := b0_1lcSideWitnesses_safe w hw m hm
        intro k d hk hd
        exact Nat.le_trans (hb k d hk hd) hB
      · rcases List.mem_cons.mp htail with hHeldMem | htail
        · have he : q = held := by simpa using hHeldMem
          subst q
          exact hHeld m hm
        · rcases List.mem_cons.mp htail with hCycleMem | htail
          · have he : q = table := by simpa using hCycleMem
            subst q
            exact (BB6.Agent50Raw10Box8.cover B).sound hm
          · rcases List.mem_cons.mp htail with hHaltMem | htail
            · have he : q = haltTable := by simpa using hHaltMem
              subst q
              have h7014 := BB6.Agent50Raw10Box0Halt.cover.sound hm
              intro k d hk hd
              exact Nat.le_trans (h7014 k d hk hd) hB
            · have he : q = candidateLeaf := by
                simpa using List.mem_singleton.mp htail
              subst q
              exact (candidateLeafCover B).sound hm)
    hOpen

/-- Conditional exact-BB6 composition; all 49 raw10 residual boxes and every
    other canonical roster entry are still required at the same score B. -/
theorem exact_from_raw10_remainder_with_candidate (B : Nat)
    (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible held m → WeightedBound B m)
    (hOpen : ∀ r ∈ raw10RemainderWithCandidate,
      ∀ m, Fits r m → WeightedBound B m)
    (hOther : ∀ e ∈ BB6.Agent47Canonical78.roster,
      e.2 ≠ firstOneB0_1LC → Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B := by
  apply BB6.Agent47Canonical78.exact_at_target B hB _ champ
  intro e he
  by_cases h : e.2 = firstOneB0_1LC
  · rw [h]
    exact raw10CoverWithCandidate B hB hHeld hOpen
  · exact hOther e he h

#print axioms original_eq_candidate
#print axioms original_never
#print axioms candidate_never
#print axioms candidate_first_hole_path
#print axioms candidateWeightedLeaf
#print axioms candidateLeaf_box0_contains
#print axioms candidateLeaf_parent
#print axioms raw10RemainderWithCandidate_exact
#print axioms raw10RemainderWithCandidate_disjoint
#print axioms raw10RemainderWithCandidate_count
#print axioms raw10RemainderWithCandidate_mass
#print axioms raw10CoverWithCandidate
#print axioms exact_from_raw10_remainder_with_candidate

end BB6.Agent19Raw10CryptidsLeaf
