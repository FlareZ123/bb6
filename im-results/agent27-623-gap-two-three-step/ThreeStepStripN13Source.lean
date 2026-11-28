import ThreeStepStripN11Source
import RootMassGapN11N12

/-!
# Finite-scale exclusion composed with an all-depth #623 halting criterion

Agent48's exact blank-root mass corridors exclude both source ratio strips
in ternary depth bands 11 and 12; the depth-10 case is already imported.
The resulting conclusion begins at n >= 13, without a finite-time cutoff
on the original machine or the infinite root orbit.
-/

namespace BB6.Agent27ThreeStepN13Source

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent48RootMassGapN11N12
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepN11Source

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem no_n11_thin_strip_root (t u v : Nat)
    (hroot : run t = some (.D u v))
    (hlo : 3^10-3 ≤ min u v) (hhi : min u v+3 < 3^11)
    (hs : thinStrip u v 11) : False := by
  have h10 : 3^10-3=59046 := by decide
  have h11 : 3^11=177147 := by decide
  rw [h10] at hlo
  rw [h11] at hhi
  have hmhi : min u v ≤ 177143 := by omega
  unfold thinStrip at hs
  dsimp at hs
  rcases hs with hs | hs
  · have hgap : absDiff (max u v) (13*min u v) ≤ 505 := by
      unfold absDiff
      split <;> omega
    exact n11_far_ratio_root_excluded t u v hroot hlo hmhi hgap
  · have hgap : absDiff (4*max u v) (7*min u v) ≤ 505 := by
      unfold absDiff
      split <;> omega
    exact n11_near_ratio_root_excluded t u v hroot hlo hmhi hgap

theorem no_n12_thin_strip_root (t u v : Nat)
    (hroot : run t = some (.D u v))
    (hlo : 3^11-3 ≤ min u v) (hhi : min u v+3 < 3^12)
    (hs : thinStrip u v 12) : False := by
  have h11 : 3^11-3=177144 := by decide
  have h12 : 3^12=531441 := by decide
  rw [h11] at hlo
  rw [h12] at hhi
  have hmhi : min u v ≤ 531437 := by omega
  unfold thinStrip at hs
  dsimp at hs
  rcases hs with hs | hs
  · have hgap : absDiff (max u v) (13*min u v) ≤ 540 := by
      unfold absDiff
      split <;> omega
    exact n12_far_ratio_root_excluded t u v hroot hlo hmhi hgap
  · have hgap : absDiff (4*max u v) (7*min u v) ≤ 540 := by
      unfold absDiff
      split <;> omega
    exact n12_near_ratio_root_excluded t u v hroot hlo hmhi hgap

/-- Every halting six-state source machine #623 would have a genuine
blank-root third-predecessor at depth at least 13 in the sharpened gate.
No assertion that this ever occurs is made. -/
theorem target_halt_implies_n13_thin_strip (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 13≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ thinStrip u v n := by
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ :=
    target_halt_implies_n11_thin_strip hh
  have hn13 : 13≤n := by
    by_contra h
    have hcases : n=11 ∨ n=12 := by omega
    rcases hcases with h11 | h12
    · subst n
      exact (no_n11_thin_strip_root t u v hq hlo hhi hs).elim
    · subst n
      exact (no_n12_thin_strip_root t u v hq hlo hhi hs).elim
  exact ⟨t,u,v,n,hq,hn13,hlo,hhi,hs⟩

theorem target_not_halt_of_n13_thin_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 13≤n →
      3^(n-1)-3≤min u v → min u v+3<3^n → ¬ thinStrip u v n) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ :=
    target_halt_implies_n13_thin_strip hh
  exact avoid t u v n hq hn hlo hhi hs

#print axioms no_n11_thin_strip_root
#print axioms no_n12_thin_strip_root
#print axioms target_halt_implies_n13_thin_strip
#print axioms target_not_halt_of_n13_thin_avoidance

end BB6.Agent27ThreeStepN13Source
