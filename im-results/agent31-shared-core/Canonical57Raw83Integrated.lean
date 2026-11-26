import Canonical57Raw83Membership
import Canonical58SixParentIntegrated
import A10Raw83Exact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31Canonical57Integrated

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31StableParentBatch
open BB6.Agent31Canonical58Membership
open BB6.Agent31Canonical58Integrated
open BB6.Agent31Canonical57Membership
open BB6.Agent29Raw83Canonical58Membership
open BB6.Agent10Raw83
open BB6ChampionArithmetic

abbrev p83Source : PartialMachine := BB6.Agent10Raw83.parent

/-- The exact table selected by the Canonical58 membership check is the
    source-accepted Raw83 parent used by the 514 Cover. -/
theorem p83_source_eq : p83 = p83Source :=
  sameTable_sound (by decide)

/-- Raw83's source-accepted exact 514 Cover lifted to the common champion
    score floor. -/
theorem p83_cover : Cover (WeightedBound 6766859) p83 := by
  rw [p83_source_eq]
  refine Cover.leaf _ ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (BB6.Agent10Raw83.all_completions m hm k d hk hd) (by decide)

/-- The seventh-parent consumer: apply the Raw83 Cover to the already
    accepted six-parent Canonical58 soundness theorem, leaving roster57. -/
theorem sound57_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster57, TNFQuotientCompatible e.2 m := by
  apply removeParents_sound
    (parents := [p83])
    (roster := BB6.Agent31Canonical58Membership.roster58)
    BB6.Agent31Canonical58Integrated.sound58_integrated
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact BB6.Agent31Canonical57Membership.p83_root
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact p83_cover

/-- Conditional exactness at any target above the champion score, assuming
    Covers only for the 57 exact residual representatives. -/
theorem exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster57, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB sound57_integrated hLeaves champ

/-- Fixed-score consumer at the existing champion score, conditional only on
    the remaining 57 Covers. -/
theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster57,
      Cover (WeightedBound (proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves + 7) :=
  exact_at_target (proposedTM63Moves + 7)
    BB6.Agent38ChampionThreshold.champion_score_ge_6766859
    hLeaves
    BB6Coverage.Agent48DirectRoot.champion_raw_witness

#print axioms BB6.Agent31Canonical57Integrated.p83_source_eq
#print axioms BB6.Agent31Canonical57Integrated.p83_cover
#print axioms BB6.Agent31Canonical57Integrated.sound57_integrated
#print axioms BB6.Agent31Canonical57Integrated.exact_at_target
#print axioms BB6.Agent31Canonical57Integrated.exact_at_champion_score

end BB6.Agent31Canonical57Integrated
