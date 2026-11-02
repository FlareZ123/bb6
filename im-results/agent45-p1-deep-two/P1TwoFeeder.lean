import P1ResidualReach
import P1TwoRoot

namespace BB6.Agent45TwoRoot
open BB6.P1Reduction

/-- Complete all-time reduction of n≡2 mod16 critical hubs to exactly
    two positive-odd feeders. The third inverse is excluded by
    the original even-positive power shape invariant. -/
theorem root_requires_one_of_two (u : Nat) (hu : u%2=1) (hge : 3≤u)
    (hr : BB6.Agent1.Reach (8*u+4) 3) :
    BB6.Agent1.Reach (4*u-4) (4*u+9) ∨
    BB6.Agent1.Reach (6*u-2) (2*u+5) := by
  have hno : ∀ k, ¬GAncestor (8*u+4) 3 k 1 := by
    intro k h
    rcases root_inverse_three u k 1 hu h with
      ⟨_,hc⟩ | ⟨_,hc⟩ | ⟨_,hc⟩ <;> omega
  obtain ⟨k,v,hanc,hv,hreach⟩ := BB6.Agent50P1.positive_G_feeder
    (8*u+4) 3 (by omega) (by omega) (by omega) hno hr
  rcases root_inverse_three u k v hu hanc with
    ⟨hk,hc⟩ | ⟨hk,hc⟩ | ⟨hk,hc⟩
  · left
    have hb : 2*k-4=4*u-4 := by omega
    have hd : v+4=4*u+9 := by omega
    simpa only [hb,hd] using hreach
  · right
    have hb : 2*k-4=6*u-2 := by omega
    have hd : v+4=2*u+5 := by omega
    simpa only [hb,hd] using hreach
  · have hb : (2*k-4)%2=0 := by omega
    have hd : (v+4)%2=0 := by omega
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape
      (2*k-4) (v+4) hreach hb (by omega) hd
    omega

#print axioms root_requires_one_of_two
end BB6.Agent45TwoRoot
