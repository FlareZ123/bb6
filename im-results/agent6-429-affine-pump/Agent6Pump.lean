import BB429Rank
import BB429Burst
import BB429DyadicStarts
import Lean.Elab.Tactic.Omega

namespace Agent6Pump
set_option maxHeartbeats 10000000

/-- A guarded two-non-first transition returns to first counter 11, with a
rank increment that is independent of the intermediate counters. -/
theorem double_reset (u b w L : Nat)
    (hb : 3 ≤ b) (hodd : b % 2 = 1)
    (hd : 4 ≤ u-b/2) (heven : (u-b/2)%2=0)
    (hexit : b ≤ (u-b/2)+7)
    (hrank : 2*u+b=22+w+3*L) :
    BB429.run 2 (u,b) = some (11,w+3*L+31) := by
  let d := u-b/2
  have hdu : 4≤d := hd
  have hdpar : d%2=0 := heven
  have hlt : b<2*u := by dsimp [d] at hdu; omega
  have hnon : b≠1 := by omega
  have hodds : b%2≠0 := by omega
  have hnext : BB429.next (u,b)=some (d+7,2*b-4) := by
    simp [BB429.next,show ¬(b≥2*u+3) by omega,
      show b≠2*u+2 by omega,show b≠2*u+1 by omega,
      show b≠2*u by omega, hodds,
      show u-b/2≠1 by omega,show u-b/2≠2 by omega,
      heven,hnon, d]
  have hh : 2*b-4<2*(d+7) := by omega
  have hposteven : (2*b-4)%2=0 := by omega
  have hpostgap : (d+7)-(2*b-4)/2=d+9-b := by omega
  have hpostevenD : ((d+7)-(2*b-4)/2)%2=0 := by omega
  have hpostnotone : (d+7)-(2*b-4)/2≠1 := by omega
  have hnext2 : BB429.next (d+7,2*b-4)=some (11,2*(d+7)+(2*b-4)-2) := by
    simp [BB429.next,show ¬(2*b-4≥2*(d+7)+3) by omega,
      show 2*b-4≠2*(d+7)+2 by omega,
      show 2*b-4≠2*(d+7)+1 by omega,
      show 2*b-4≠2*(d+7) by omega,
      hposteven,hpostnotone,hpostevenD]
  have hval : 2*(d+7)+(2*b-4)-2=w+3*L+31 := by
    dsimp [d]
    omega
  simp [BB429.run,hnext,hnext2,hval]

/-- Every successful first-only prefix followed by these two non-first cases
is an authentic L+2-step source macro pump (11,w) -> (11,w+3L+31). -/
theorem pump (L w u b : Nat)
    (hfirst : BB429Burst.firstRun L (11,w)=some (u,b))
    (hb : 3 ≤ b) (hodd : b % 2 = 1)
    (hd : 4 ≤ u-b/2) (heven : (u-b/2)%2=0)
    (hexit : b ≤ (u-b/2)+7) :
    BB429.run (L+2) (11,w)=some (11,w+3*L+31) := by
  have hp := BB429Burst.prefix_formula 11 w L u b hfirst
  have htwo := double_reset u b w L hb hodd hd heven hexit (by omega)
  rw [BB429.run_add]
  simp [BB429DyadicStarts.first_prefix_is_source _ _ _ hfirst,htwo]

#print axioms double_reset
#print axioms pump
end Agent6Pump
