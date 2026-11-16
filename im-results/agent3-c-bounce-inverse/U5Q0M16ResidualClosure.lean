import U5Q0M16Core
import U5Q0M16Residual
import U5M8Q0Partial
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5M16ResidualClosure
open BB6.Agent3

private theorem q0_parent_reach_implies_X (t : Nat) (ht : 1≤t) :
    CReach (64*t+5) (32*t+3) → CReach (44*t-1) (42*t-1) := by
  intro hP
  have hOdd := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (64*t+5) (32*t+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp hP
  have hEven := (BB6.Agent3.evenodd_four_blank_reach_iff
    (48*t+2) (40*t+1)
    (by omega) (by omega) (by omega) (by omega)).mp hOdd
  exact hEven

/-- For every U5 residual with w=21 (mod 32), the exceptional q=0
    predecessor of its y=3 terminal is unreachable. The residual identity
    forces t=19 (mod 32), and the source-certified M16 quotient excludes
    every predecessor of the two-step feeder X_t. -/
theorem blank_no_u5_q0_parent_w21 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%32=21)
    (ht : 1≤t) :
    ¬ CReach (8*(m+1)-3) (4*(m+1)-1) := by
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod32 w s m t hs hm hp hw
  have htform : t=32*(t/32)+19 := by omega
  have hX := BB6.Agent3U5Q0M16.q0_X_not_reach t (t/32) htform
  intro hP
  have hP' : CReach (64*t+5) (32*t+3) := by
    have hx : 8*(m+1)-3=64*t+5 := by omega
    have hy : 4*(m+1)-1=32*t+3 := by omega
    simpa only [hx,hy] using hP
  exact hX (q0_parent_reach_implies_X t ht hP')
end BB6.Agent3U5M16ResidualClosure
