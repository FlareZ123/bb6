import ThreeStepStripWeightedSkewSource
import ThreeStepStripN13Source

/-!
# Composed all-depth skew predecessor gate beyond the first three bands

Source-finite root exclusions at ternary depths 10,11,12 combine with the
genuine six-state weighted skew predecessor theorem to force n>=13.
The remaining unbounded root avoidance premise is intentionally explicit.
-/

namespace BB6.Agent27ThreeStepSkewN13Source

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepWeightedSkewSource
open BB6.Agent27ThreeStepN11Source
open BB6.Agent27ThreeStepN13Source

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The sector-specific signed gate is strictly contained in the
source-certified 35n/23n predecessor gate for n>=10. -/
theorem skew_implies_thin (n u v : Nat) (hn : 10≤n)
    (hs : skewStrip u v n) : thinStrip u v n := by
  unfold skewStrip at hs
  unfold thinStrip
  dsimp at *
  rcases hs with hs | hs
  · left
    omega
  · right
    omega

theorem target_halt_implies_n13_skew_strip (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 13≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ skewStrip u v n := by
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ :=
    target_halt_implies_skew_strip hh
  have hthin := skew_implies_thin n u v hn hs
  have hn13 : 13≤n := by
    by_contra h
    have hcases : n=10 ∨ n=11 ∨ n=12 := by omega
    rcases hcases with h10 | hhrest
    · subst n
      exact (no_n10_thin_strip_root t u v hq hlo hhi hthin).elim
    · rcases hhrest with h11 | h12
      · subst n
        exact (no_n11_thin_strip_root t u v hq hlo hhi hthin).elim
      · subst n
        exact (no_n12_thin_strip_root t u v hq hlo hhi hthin).elim
  exact ⟨t,u,v,n,hq,hn13,hlo,hhi,hs⟩

theorem target_not_halt_of_n13_skew_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 13≤n →
      3^(n-1)-3≤min u v → min u v+3<3^n → ¬ skewStrip u v n) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ :=
    target_halt_implies_n13_skew_strip hh
  exact avoid t u v n hq hn hlo hhi hs

#print axioms skew_implies_thin
#print axioms target_halt_implies_n13_skew_strip
#print axioms target_not_halt_of_n13_skew_avoidance

end BB6.Agent27ThreeStepSkewN13Source
