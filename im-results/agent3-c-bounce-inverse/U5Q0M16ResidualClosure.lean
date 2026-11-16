import U5Q0M16Core
import U5Q0M16Residual
import U5M8Q0Partial
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3U5M16ResidualClosure
open BB6.Agent3

private theorem q0_parent_reach_implies_X (t : Nat) (ht : 1≤t)
    (h : CReach (64*t+5) (32*t+3)) :
    CReach (44*t-1) (42*t-1) := by
  have h1 := (BB6.Agent3.oddodd_val3_blank_reach_iff
    (64*t+5) (32*t+3)
    (by omega) (by omega) (by omega) (by omega) (by omega)).mp h
  have h1' : CReach (48*t+2) (40*t+1) := by
    have hx : ((64*t+5)+(32*t+3)-4)/2=48*t+2 := by omega
    have hy : ((64*t+5)+3*(32*t+3)-10)/4=40*t+1 := by omega
    simpa only [hx,hy] using h1
  have h2 := (BB6.Agent3.evenodd_four_blank_reach_iff
    (48*t+2) (40*t+1)
    (by omega) (by omega) (by omega) (by omega)).mp h1'
  have h2' : CReach (44*t-1) (42*t-1) := by
    have hx : ((48*t+2)+(40*t+1)-5)/2=44*t-1 := by omega
    have hy : ((48*t+2)+3*(40*t+1)-9)/4=42*t-1 := by omega
    simpa only [hx,hy] using h2
  exact h2'


/-- The q=0 member of the U5 parent fan is unreachable on the
    w=21 (mod 32) residual cylinder: its exact two-step pullback is
    X_t, and the residual equations force t=19 (mod 32), where the
    source-certified M16 quotient excludes every source parent. -/
theorem blank_no_u5_q0_parent_w21 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%32=21)
    (ht : 1≤t)
    (hparent : CReach (64*t+5) (32*t+3)) : False := by
  have hX := q0_parent_reach_implies_X t ht hparent
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod32
    w s m t hs hm hp hw
  obtain ⟨n,hn⟩ : ∃ n, t=32*n+19 := by
    refine ⟨t/32,?_⟩
    omega
  exact BB6.Agent3U5Q0M16.q0_X_not_reach t n hn hX

/-- The q=0 member of the U5 parent fan is unreachable on the
    additional w=37 (mod128) cylinder: its exact two-step pullback is
    X_t with t=99 (mod128), where the M16 quotient excludes every
    possible original-source parent. -/
theorem blank_no_u5_q0_parent_w37 (w s m t : Nat)
    (hs : 211*s+129=5*2^(201+3360*w))
    (hm : 32*s=32+840*w+m)
    (hp : m+1=8*t+1)
    (hw : w%128=37)
    (ht : 1≤t)
    (hparent : CReach (64*t+5) (32*t+3)) : False := by
  have hX := q0_parent_reach_implies_X t ht hparent
  have htmod := BB6.Agent3U5M16Residual.u5_m8_t_mod128_w37
    w s m t hs hm hp hw
  obtain ⟨n,hn⟩ : ∃ n, t=128*n+99 := by
    refine ⟨t/128,?_⟩
    omega
  exact BB6.Agent3U5Q0M16.q0_X_not_reach_t99 t n hn hX

end BB6.Agent3U5M16ResidualClosure
