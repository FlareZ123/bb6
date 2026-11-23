import RayOddForkExtended

set_option maxHeartbeats 0

namespace CascadeTerminalFirstFork
open CascadeResetInverse CascadeRayOddStrip CascadeSweep

/-- The t=1 odd feeder of the nonterminal J-2 canonical ray
    cannot be blank-rooted when its output quotient is 1 mod 3.
    All hypotheses are exact arithmetic consequences of the high-c
    original #746 ray formula and X_-/27 residue 9. -/
theorem tone_feeder_nonterminal_gap_dead
    (n p q d h : Nat)
    (hn : 257 ≤ n)
    (hp : p = 2^n)
    (hpbig : n+16 < p)
    (hqlow : 7*p < 4*q)
    (hqhigh : q < 2*p)
    (hlin : 9*h + 2*q+n+15 = 14*p)
    (hsector : (2*p+n)%3 = 0)
    (hd : d%3 = 1)
    (hsource : h+2*p+n+3 = 4*d) :
    ¬ ReachC (2,0) (h,0) := by
  have hl : 2^n < h := by rw [←hp]; omega
  have hu : 2*h+2 < 3*2^n := by rw [←hp]; omega
  have hres : h%3 ≠ 2 := by omega
  exact root_excludes_nonimage h hres
    (gap_avoids_even_images n h (by omega) hl hu)

/-- The arithmetic heart of the 3-adic period-three selector:
    at least one of three consecutive even-index ancestors has
    odd-parent numerator divisible by nine. -/
theorem three_even_depth_residue_gate (A B : Nat)
    (hA : A%3=1) (hB : B%3=1) :
    (2*(A+B)+5)%9=0 ∨
    (2*(A+4*B)+5)%9=0 ∨
    (2*(A+16*B)+5)%9=0 := by
  omega

#print axioms tone_feeder_nonterminal_gap_dead
#print axioms three_even_depth_residue_gate
end CascadeTerminalFirstFork
