import Raw41LB0LCGraft
import Raw41LD0LCClosed
import Raw41LB0RBClosed
import Raw41LC1LBClosed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw41
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot

/-- Remove a finite list of individually certified quotient families. -/
def removeTargets : List PartialMachine → List (List Move × PartialMachine) → List (List Move × PartialMachine)
  | [],xs => xs
  | p::ps,xs => removeTargets ps (xs.filter fun e => !(sameTable e.2 p))

theorem removeTargets_sound {ps : List PartialMachine} {xs : List (List Move × PartialMachine)} {B : Nat}
    (hs : ∀ m, compatible root m → WeightedBound B m ∨ ∃ e ∈ xs, TNFQuotientCompatible e.2 m)
    (hp : ∀ p ∈ ps, ∀ m, TNFQuotientCompatible p m → WeightedBound B m) :
    ∀ m, compatible root m → WeightedBound B m ∨ ∃ e ∈ removeTargets ps xs, TNFQuotientCompatible e.2 m := by
  induction ps generalizing xs with
  | nil => exact hs
  | cons p ps ih =>
    exact ih (filter_sound p hs (hp p (List.mem_cons_self))) (fun q hq => hp q (List.mem_cons_of_mem p hq))

abbrev batchTargets : List PartialMachine := [Raw41LD0LC_p,Raw41LB0RB_p,Raw41LC1LB_p]
noncomputable def afterBatch := removeTargets batchTargets afterLB0LC

theorem batchTargets_bound : ∀ p ∈ batchTargets, ∀ m, TNFQuotientCompatible p m → WeightedBound 7014 m := by
  intro p hp
  simp only [batchTargets,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact fun m hm k d hk hd => Nat.le_trans (Raw41LD0LC_bound m hm k d hk hd) (by decide)
  · exact fun m hm k d hk hd => Nat.le_trans (Raw41LB0RB_bound m hm k d hk hd) (by decide)
  · exact fun m hm k d hk hd => Nat.le_trans (Raw41LC1LB_bound m hm k d hk hd) (by decide)

theorem afterBatch_count : afterBatch.length = 224 := by decide +kernel

theorem afterBatch_sound : ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterBatch, TNFQuotientCompatible e.2 m :=
  removeTargets_sound afterLB0LC_sound batchTargets_bound

noncomputable def afterSix := afterBatch.filter fun e => !(sameTable e.2 lc0lbParent)
theorem afterSix_count : afterSix.length = 223 := by decide +kernel

theorem afterSix_sound (hLC0LB : ∀ m, TNFQuotientCompatible lc0lbParent m → WeightedBound 229 m) :
    ∀ m, compatible root m → WeightedBound 7014 m ∨ ∃ e ∈ afterSix, TNFQuotientCompatible e.2 m :=
  filter_sound _ afterBatch_sound (fun m hm k d hk hd => Nat.le_trans (hLC0LB m hm k d hk hd) (by decide))

theorem exact_at_target_after_Batch (B : Nat) (hB : 7014 ≤ B)
    (hLeaves : ∀ e ∈ afterBatch, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  exact_from_quotient_roster (by omega) hB afterBatch_sound hLeaves champ

#print axioms removeTargets_sound
#print axioms afterBatch_count
#print axioms afterBatch_sound
#print axioms afterSix_count
#print axioms afterSix_sound
#print axioms exact_at_target_after_Batch
end BB6.Agent47Raw41
