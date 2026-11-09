import W2FullHeadMax
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2FullPhysicalMax

open BB6Coverage BB429PhysicalFrontier BB429PhysicalBridge
open BB429DeltaPhysicalBridge BB429OddExcursion
open BB429SourceE1Return BB429SourceE1Delta
open BB429W4HeadMax BB429W4HeadPrefix BB429W2FullHeadMax

/-- General physical maximal-head transfer. A successfully certified
    original-table zipper run gives an exact *all-primitive-prefix* upper
    bound on the raw physical head coordinate for every represented tape.
    Both the run semantics and the representation relation are unchanged. -/
theorem physical_runWithMax_bound
    (n t : Nat) (start : Zipper) (c : Config)
    (hrep : Represents start c) (out : Zipper × Int × Int)
    (hfull : runWithMax n start = some out)
    (ht : t ≤ n) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t c = some c' ∧
      c'.head ≤ c.head + out.2.2 := by
  have hfullDelta : runWithDelta n start = some (out.1,out.2.1) := by
    have hproj := runWithMax_toDelta n start
    simpa [hfull] using hproj.symm
  have hlen : n = t + (n-t) := by omega
  cases hprefix : runWithDelta t start with
  | none =>
      rw [hlen,runWithDelta_add,hprefix] at hfullDelta
      simp at hfullDelta
  | some q =>
      have hproj := runWithMax_toDelta t start
      cases hprefixMax : runWithMax t start with
      | none =>
          simp [hprefixMax,hprefix] at hproj
      | some p =>
          have hdelta : p.2.1 = q.2 := by
            simp [hprefixMax,hprefix] at hproj
            exact hproj.2
          have hfull' : runWithMax (t+(n-t)) start = some out := by
            rw [← hlen]
            exact hfull
          have hbound := runWithMax_prefix_le t (n-t) start
            p hprefixMax out hfull'
          obtain ⟨c',hrun,hrep',hdisp⟩ :=
            source_runWithDelta_rep t start c hrep q.1 q.2 hprefix
          refine ⟨c',hrun,?_⟩
          omega

/-- Source-certified head barrier over every primitive prefix of the
    entire EVEN right-two Junc return in the actual six-state physical machine. -/
theorem physical_even_w2_entire_prefix_bound
    (k t : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k) 2) c)
    (ht : t ≤ 38*k+204) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t c = some c' ∧
      c'.head ≤ c.head + ((4*k+11 : Nat) : Int) := by
  exact physical_runWithMax_bound (38*k+204) t (junc 0 (2*k) 2) c hrep
    (junc 0 0 (4*k+18), -10, ((4*k+11 : Nat) : Int))
    (w2_all_even_max k) ht

/-- Analogous actual-physical head barrier for every ODD right-two Junc
    parameter, including the exceptional base k=0. -/
theorem physical_odd_w2_entire_prefix_bound
    (k t : Nat) (c : Config)
    (hrep : Represents (junc 0 (2*k+1) 2) c)
    (ht : t ≤ 44*k+266) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t c = some c' ∧
      c'.head ≤ c.head + ((4*k+17 : Nat) : Int) := by
  exact physical_runWithMax_bound (44*k+266) t (junc 0 (2*k+1) 2) c hrep
    (junc 0 0 (4*k+24), -10, ((4*k+17 : Nat) : Int))
    (w2_all_odd_max k) ht

#print axioms physical_runWithMax_bound
#print axioms physical_even_w2_entire_prefix_bound
#print axioms physical_odd_w2_entire_prefix_bound

end BB429W2FullPhysicalMax
