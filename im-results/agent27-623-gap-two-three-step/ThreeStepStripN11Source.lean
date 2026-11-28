import ThreeStepStripSource
import RootMassGapAllN10

/-!
# First all-scale terminal-strip depth after authentic root exclusion of n=10

The source-certified all-scale third-predecessor criterion is restricted
to n >= 11 by composing the independent full n=10 root-gap exclusion.
This does not claim the remaining infinite bands are avoided.
-/

namespace BB6.Agent27ThreeStepN11Source

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent8RootMassGapAllN10
open BB6.Agent27ThreeStepStripSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Every n=10 predecessor in either strictly sharpened source strip
is forbidden on the genuine blank-root orbit. The 470-width root theorem
is already strong enough, with no further finite simulation. -/
theorem no_n10_thin_strip_root (t u v : Nat)
    (hroot : run t = some (.D u v))
    (hlo : 3^9-3 ≤ min u v) (hhi : min u v+3 < 3^10)
    (hs : thinStrip u v 10) : False := by
  have h9 : 3^9-3=19680 := by decide
  have h10 : 3^10=59049 := by decide
  rw [h9] at hlo
  rw [h10] at hhi
  have hmhi : min u v ≤ 59045 := by omega
  unfold thinStrip at hs
  dsimp at hs
  rcases hs with hs | hs
  · have hgap : absDiff (max u v) (13*min u v) ≤ 470 := by
      unfold absDiff
      split <;> omega
    exact n10_far_ratio_root_excluded t u v hroot hlo hmhi hgap
  · have hgap : absDiff (4*max u v) (7*min u v) ≤ 470 := by
      unfold absDiff
      split <;> omega
    exact n10_near_ratio_root_excluded t u v hroot hlo hmhi hgap

/-- Source-level six-state halting necessary condition: all candidates must
occur at logarithmic depth at least eleven, with separate near/far widths. -/
theorem target_halt_implies_n11_thin_strip (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 11≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ thinStrip u v n := by
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ :=
    target_halt_implies_thin_strip hh
  have hn11 : 11≤n := by
    by_contra h
    have heq : n=10 := by omega
    subst n
    exact (no_n10_thin_strip_root t u v hq hlo hhi hs).elim
  exact ⟨t,u,v,n,hq,hn11,hlo,hhi,hs⟩

/-- To establish actual nonhalting, the remaining all-time root avoidance
must be proved only at depths n>=11. This missing premise is explicit. -/
theorem target_not_halt_of_n11_thin_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 11≤n →
      3^(n-1)-3≤min u v → min u v+3<3^n → ¬ thinStrip u v n) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ :=
    target_halt_implies_n11_thin_strip hh
  exact avoid t u v n hq hn hlo hhi hs

#print axioms no_n10_thin_strip_root
#print axioms target_halt_implies_n11_thin_strip
#print axioms target_not_halt_of_n11_thin_avoidance

end BB6.Agent27ThreeStepN11Source
