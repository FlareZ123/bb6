import Raw36D1Fifteen
import Raw36Branch
import Raw36B106
import Raw36B107
import Raw36B108
import Raw36B1RD
import Raw36B110
import Raw36B112
import Raw36B113
import Raw36B114
import Raw36B118
import Raw36B120

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot

/-- Exact remaining B1 representatives of the D1=1LB cylinder. -/
def b1Complement : List Move := [⟨false,false,1⟩,⟨false,false,4⟩,⟨true,false,4⟩,⟨true,true,4⟩]

theorem b1Complement_count : b1Complement.length = 4 := by decide
theorem b1Complement_nodup : b1Complement.Nodup := by decide

/-- Every completion of the original seven-hole parent is bounded if
    the four remaining concrete B1 cylinders are bounded. The eleven
    others use the existing source-accepted exact-table certificates. -/
theorem d1_bound_from_four (B : Nat) (hB : 1022 ≤ B)
    (h : ∀ mv ∈ b1Complement, ∀ m,
      compatible (b1Child mv) m → WeightedBound B m)
    (m : Machine) (hm : compatible d1 m) : WeightedBound B m := by
  apply d1_bound_from_fifteen B (by omega) _ m hm
  intro mv hmv m' hc
  simp only [b1Retained, List.mem_cons, List.not_mem_nil, or_false] at hmv
  rcases hmv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36.branch_bound m' hc k d hk hd) (by omega)
  · exact h ⟨false,false,1⟩ (by decide) m' hc
  · exact h ⟨false,false,4⟩ (by decide) m' hc
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B106.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B107.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B108.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B1RD.rd_bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B110.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B112.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B113.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B114.bound m' hc k d hk hd) (by omega)
  · exact h ⟨true,false,4⟩ (by decide) m' hc
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B118.bound m' hc k d hk hd) (by omega)
  · intro k d hk hd
    exact Nat.le_trans (BB6.Agent29Raw36B120.bound m' hc k d hk hd) (by omega)
  · exact h ⟨true,true,4⟩ (by decide) m' hc

theorem d1_cover_from_four (B : Nat) (hB : 1022 ≤ B)
    (h : ∀ mv ∈ b1Complement, Cover (WeightedBound B) (b1Child mv)) :
    Cover (WeightedBound B) d1 := by
  apply Cover.leaf
  intro m hm
  exact d1_bound_from_four B hB
    (by intro mv hmv m hc; exact (h mv hmv).sound m hc) m hm

#print axioms b1Complement_count
#print axioms b1Complement_nodup
#print axioms d1_bound_from_four
#print axioms d1_cover_from_four
end BB6.Agent29Raw36
