import BB429ZeroTwoStrengthened
import BB429OddResetImproved
import Lean.Elab.Tactic.Omega

/-!
# Stronger authentic blank-root zero-two gateway: 21/32 diagonal filters

Assuming a genuine root input with first counter >=129 and an output
(0,z) with z=2 mod4, combine the sharp four-class upper-boundary row
with the newly source-proven three-class odd-reset row.

This is an exact all-natural conditional statement about one all-F
inverse feeder. It does not close the other S-parent inverse families,
the z=0 mod4 predecessors, or the original Turing machine.
-/

namespace BB429ZeroTwoThree

open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- Every sufficiently large blank-root predecessor to a zero-two state
    uses exactly one of the two branches, with four or three possible
    parent residues respectively. -/
theorem rooted_zero_two_gateway_three (n u w z : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z))
    (hz : z%4=2) (hu : 129 ≤ u) :
    (w=2*u+2 ∧ z=4*u+18 ∧
     (u%16=0 ∨ u%16=5 ∨ u%16=8 ∨ u%16=13)) ∨
    (w+3=2*u ∧ z=4*u+2 ∧
     (u%32=13 ∨ u%32=15 ∨ u%32=29)) := by
  rcases BB429ZeroTwoStrengthened.rooted_zero_two_gateway_upper_four
    n u w z hr hs hz hu with
    ⟨hw,hzout,hrows⟩ | ⟨hw,hzout,hrows⟩
  · exact Or.inl ⟨hw,hzout,hrows⟩
  · have hrOdd : Reach u w := ⟨n,hr⟩
    have h3 := BB429OddResetImproved.rooted_odd_reset_necessary_three
      u w hrOdd hu hw
    exact Or.inr ⟨hw,hzout,h3⟩

/-- For J=4m+2 and z congruent to the exact low-nine zero feeder,
    only 11 m-residues mod32 survive, excluding 21/32. -/
theorem diagonal_zero_two_m_necessary_eleven (n u w z m : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z))
    (hz : z%4=2) (hu : 129 ≤ u)
    (hfeeder : (z+12*m)%128=30) :
    m%32=1 ∨ m%32=2 ∨ m%32=8 ∨ m%32=9 ∨
    m%32=10 ∨ m%32=14 ∨ m%32=17 ∨
    m%32=18 ∨ m%32=25 ∨ m%32=26 ∨ m%32=30 := by
  rcases rooted_zero_two_gateway_three n u w z hr hs hz hu with
    ⟨hw,hzout,hcls⟩ | ⟨hw,hzout,hcls⟩
  · omega
  · omega

private theorem pow_mod128_zero (e : Nat) (he : 7 ≤ e) :
    (2:Nat)^e % 128 = 0 := by
  have heq : e=7+(e-7) := by omega
  rw [heq, Nat.pow_add, show (2:Nat)^7=128 by decide]
  omega

/-- All-natural specialization to the genuine diagonal J exponent
    equation. The parent first counter bound is the only nonautomatic
    size assumption. -/
theorem diagonal_zero_two_m_power_eleven (n u w z m J N : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z))
    (hz : z%4=2) (hu : 129 ≤ u)
    (hJ : J=4*m+2) (hJlarge : 3 ≤ J) (hNlarge : 5 ≤ N)
    (hfeeder : z+48*2^J+3*J=12*2^(N+2)+36) :
    m%32=1 ∨ m%32=2 ∨ m%32=8 ∨ m%32=9 ∨
    m%32=10 ∨ m%32=14 ∨ m%32=17 ∨
    m%32=18 ∨ m%32=25 ∨ m%32=26 ∨ m%32=30 := by
  have hpN := pow_mod128_zero (N+2) (by omega)
  have hpJ := pow_mod128_zero (J+4) (by omega)
  have hmul : 48*2^J=3*2^(J+4) := by
    rw [show J+4=4+J by omega, Nat.pow_add,
        show (2:Nat)^4=16 by decide]
    omega
  have hpowJ : (48*2^J)%128=0 := by
    rw [hmul]
    omega
  have hmod : (z+12*m)%128=30 := by omega
  exact diagonal_zero_two_m_necessary_eleven n u w z m hr hs hz hu hmod

#print axioms rooted_zero_two_gateway_three
#print axioms diagonal_zero_two_m_necessary_eleven
#print axioms diagonal_zero_two_m_power_eleven

end BB429ZeroTwoThree
