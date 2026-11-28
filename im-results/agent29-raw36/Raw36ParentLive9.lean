import Raw36ParentLive10
import Raw36B116
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- After consuming the source-accepted B1=1LE cylinder, only the nine
    direct D1 cylinders remain live under the Raw36 parent. -/
def parentLive9 : List PartialMachine := d1Complement.map d1Child

theorem b116_identity : b1Child ⟨true,false,4⟩ = BB6.Agent29Raw36B116.b1 := by rfl

theorem b116_cover_at (B : Nat) (hB : 387 ≤ B) :
    Cover (WeightedBound B) (b1Child ⟨true,false,4⟩) := by
  rw [b116_identity]
  apply Cover.leaf
  intro m hm k d hk hd
  exact Nat.le_trans (BB6.Agent29Raw36B116.bound m hm k d hk hd) hB

theorem d1_cover_closed (B : Nat) (hB : 1152 ≤ B) :
    Cover (WeightedBound B) d1 := by
  exact d1_cover_from_one B hB (b116_cover_at B (by omega))

theorem parent_cover_from_nine (B : Nat) (hB : 1152 ≤ B)
    (h : ∀ p ∈ parentLive9, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) parent := by
  apply parent_cover_from_ten B hB
  intro p hp
  unfold parentLive10 at hp
  rcases List.mem_append.mp hp with hD | hB1
  · exact h p (by simpa [parentLive9] using hD)
  · rcases List.mem_map.mp hB1 with ⟨mv,hm,rfl⟩
    have hmv : mv = ⟨true,false,4⟩ := by simpa [b1Live1] using hm
    subst mv
    exact b116_cover_at B (by omega)

theorem parentLive9_count : parentLive9.length = 9 := by decide

#print axioms b116_identity
#print axioms b116_cover_at
#print axioms d1_cover_closed
#print axioms parent_cover_from_nine
#print axioms parentLive9_count
end BB6.Agent29Raw36
