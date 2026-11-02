import P1TwoFeeder
import P1Deep2

namespace BB6.Agent45TwoRoot
open BB6.Agent1

/-- The other live root feeder is also an exact two-transition source path. -/
theorem lower_pair (u : Nat) (hu : 3 ≤ u) :
    T (4*u-4) (4*u+9) = some (4*u-1,4*u+7) ∧
    T (4*u-1) (4*u+7) = some (8*u+4,3) := by
  have he : (4*u-4)%2=0 := by omega
  have hG : G (2*u) (4*u+5) = (8*u+4,3) := by
    rw [G]
    have hnot : ¬(4*u+5<2*(2*u)) := by omega
    have hmid : ¬(4*u+5≤2*(2*u)+1) := by omega
    simp only [hnot, dite_false, hmid, ite_false]
    congr 1 <;> omega
  have hfirst : T (4*u-4) (4*u+9) = some (4*u-1,4*u+7) := by
    simp only [T, show 4*u+9≠0 by omega,show 4*u+9≠1 by omega,
      if_false,if_pos he]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega
  have hsecond : T (4*u-1) (4*u+7) = some (8*u+4,3) := by
    have hodd : (4*u-1)%2≠0 := by omega
    have hthree : 4*u+7≠3 := by omega
    have htwo : 4*u+7≠2 := by omega
    have hz : 4*u+7≠0 := by omega
    have hone : 4*u+7≠1 := by omega
    simp only [T,hz,hone,htwo,hthree,hodd,if_false]
    have hp : (4*u-1)/2+1=2*u := by omega
    have hc : 4*u+7-2=4*u+5 := by omega
    rw [hp,hc,hG]
  exact ⟨hfirst,hsecond⟩

/-- Exact iff for all positive-odd P1 critical-root shapes of the n=2 sector:
    blank reachability of the root is equivalent to blank reachability of one
    of the two explicit two-transition feeder lines. -/
theorem root_reach_iff_two_feeders (u : Nat) (hu : u%2=1) (hge : 3≤u) :
    Reach (8*u+4) 3 ↔
      Reach (4*u-4) (4*u+9) ∨ Reach (6*u-2) (2*u+5) := by
  constructor
  · exact root_requires_one_of_two u hu hge
  · intro hr
    rcases hr with hr | hr
    · obtain ⟨h1,h2⟩ := lower_pair u hge
      exact Reach.next _ _ _ _
        (Reach.next _ _ _ _ hr h1) h2
    · obtain ⟨h1,h2⟩ := BB6.Agent45Deep2.middle_pair u (by omega)
      exact Reach.next _ _ _ _
        (Reach.next _ _ _ _ hr h1) h2

#print axioms lower_pair
#print axioms root_reach_iff_two_feeders
end BB6.Agent45TwoRoot
