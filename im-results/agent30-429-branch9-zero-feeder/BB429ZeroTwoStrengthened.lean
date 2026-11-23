import BB429OddResetGate
import BB429UpperBoundary
import Lean.Elab.Tactic.Omega

/-!
# Source-exact tightening of the zero-two gateway for the diagonal feeder

The high first-coordinate upper-boundary source was previously allowed in
seven classes modulo 16. The new root-line theorem reduces it to four.
Together with the existing odd-reset six-class source theorem, this
excludes 18 of 32 m classes in J=4m+2 along the all-F low-nine route.
Other inverse routes, including every exceptional S parent, remain open.
-/

namespace BB429ZeroTwoStrengthened

set_option maxHeartbeats 25000000
set_option maxRecDepth 30000

/-- An exact zero output with second counter 2(mod4) has either
    a four-class upper input or a six-class odd-reset input,
    when its genuine root parent has sufficiently large first counter. -/
theorem rooted_zero_two_gateway_upper_four (n u w z : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z)) (hz : z%4=2)
    (hu : 129 ≤ u) :
    (w=2*u+2 ∧ z=4*u+18 ∧
     (u%16=0 ∨ u%16=5 ∨ u%16=8 ∨ u%16=13)) ∨
    (w+3=2*u ∧ z=4*u+2 ∧
     (u%32=7 ∨ u%32=13 ∨ u%32=15 ∨
      u%32=21 ∨ u%32=29 ∨ u%32=31)) := by
  rcases BB429OddResetGate.rooted_zero_two_gateway n u w z hr hs hz with
    ⟨hw,hzout⟩ | ⟨hw,hzout,hcases⟩
  · have hrup : BB429NewResidue.Reach u (2*u+2) := by
      exact ⟨n,by simpa only [hw] using hr⟩
    exact Or.inl ⟨hw,hzout,
      BB429UpperBoundary.rooted_upper_mod16 u hrup hu⟩
  · exact Or.inr ⟨hw,hzout,hcases⟩

/-- The complete all-F zero-two precursor from J=4m+2
    can pass the authentic zero-two root gateway only in
    14 explicitly listed m(mod32) classes, rather than 18. -/
theorem diagonal_zero_two_m_mod32 (n u w z m : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z))
    (hz : z%4=2) (hu : 129 ≤ u)
    (hfeeder : (z+12*m)%128=30) :
    m%32=0 ∨ m%32=1 ∨ m%32=2 ∨ m%32=6 ∨
    m%32=8 ∨ m%32=9 ∨ m%32=10 ∨ m%32=14 ∨
    m%32=17 ∨ m%32=18 ∨ m%32=24 ∨
    m%32=25 ∨ m%32=26 ∨ m%32=30 := by
  rcases rooted_zero_two_gateway_upper_four n u w z hr hs hz hu with
    ⟨hw,hzout,hcls⟩ | ⟨hw,hzout,hcls⟩
  · omega
  · omega

private theorem pow_mod128_zero (e : Nat) (he : 7 ≤ e) :
    (2:Nat)^e % 128 = 0 := by
  have heq : e=7+(e-7) := by omega
  rw [heq, Nat.pow_add, show (2:Nat)^7=128 by decide]
  omega

/-- Power-of-two specialization for the genuine last-reset diagonal
    all-F zero feeder; n is the source-run index, N=n_diag+J. -/
theorem diagonal_zero_two_m_power_mod32 (n u w z m J N : Nat)
    (hr : BB429.run n (0,0)=some (u,w))
    (hs : BB429.next (u,w)=some (0,z))
    (hz : z%4=2) (hu : 129 ≤ u)
    (hJ : J=4*m+2) (hJlarge : 3 ≤ J) (hNlarge : 5 ≤ N)
    (hfeeder : z+48*2^J+3*J=12*2^(N+2)+36) :
    m%32=0 ∨ m%32=1 ∨ m%32=2 ∨ m%32=6 ∨
    m%32=8 ∨ m%32=9 ∨ m%32=10 ∨ m%32=14 ∨
    m%32=17 ∨ m%32=18 ∨ m%32=24 ∨
    m%32=25 ∨ m%32=26 ∨ m%32=30 := by
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
  exact diagonal_zero_two_m_mod32 n u w z m hr hs hz hu hmod

#print axioms rooted_zero_two_gateway_upper_four
#print axioms diagonal_zero_two_m_mod32
#print axioms diagonal_zero_two_m_power_mod32

end BB429ZeroTwoStrengthened
