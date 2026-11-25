import Raw59CanonicalPartition
import Raw59A0RBData

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw59CanonicalPilot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent32Raw59 BB6.Agent32Raw59Partition

def closed (mv : Move) : Bool :=
  ([(⟨false,true,0⟩ : Move),⟨true,false,3⟩,⟨true,true,0⟩,
    ⟨true,true,4⟩,⟨false,true,1⟩]).any (fun a => decide (a=mv))

theorem closed_sound (mv : Move) (h : closed mv = true) :
    ∀ m, compatible (child mv) m → WeightedBound 395 m := by
  simp only [closed,List.any_cons,List.any_nil,Bool.or_false,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with h|h|h|h|h
  · subst mv; exact all_0RA
  · subst mv; exact all_1LD
  · subst mv; exact all_1RA
  · subst mv; exact all_1RE
  · subst mv; intro m hm k d hk hd
    exact Nat.le_trans (BB6.Agent32Raw59A0RB.all0RB m hm k d hk hd) (by decide)

theorem retained_count : (retained closed).length = 19 := by decide

theorem exact_at_target (B : Nat) (hB : 7014 ≤ B)
    (ho : ∀ e ∈ BB6.Agent47Canonical78.roster, e.2 ≠ p59 → Cover (WeightedBound B) e.2)
    (hr : ∀ mv ∈ retained closed, Cover (WeightedBound B) (child mv))
    (champ : ∃ m : BB6.Coverage.RawMachine, BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B :=
  BB6.Agent32Raw59Partition.exact_at_target B hB closed closed_sound ho hr champ

#print axioms closed_sound
#print axioms retained_count
#print axioms exact_at_target
end BB6.Agent32Raw59CanonicalPilot
