import ZeroRegularHeadMax
import PositiveRegularHeadMax
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429PhysicalRegularHeadMax

open BB6Coverage BB429OddExcursion BB429SourceE1Return
open BB429SourceE1Delta BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429PhysicalFrontier BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429W4HeadMax BB429W4HeadPrefix
open BB429ZeroRegularHeadMax BB429PositiveRegularHeadMax

/-- During any ordinary zero-u Junc return, the literal original #429 raw
head stays strictly left of the initially marked rightmost cell, at every
intermediate primitive step and at the terminal Junc. -/
theorem physical_zero_regular_all_prefixes_before_old_mark
    (v w t : Nat) (c : Config)
    (hrep : Represents (junc 0 v (w+3)) c) (ht : t ≤ 2*v+27) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      d.head < c.head + ((2*v+w+6 : Nat) : Int) := by
  have hfull := BB429ZeroRegularHeadMax.junc0_regular_max v w
  have hlen : 2*v+27 = t+(2*v+27-t) := by omega
  cases hpre : runWithMax t (junc 0 v (w+3)) with
  | none =>
      rw [hlen,runWithMax_add,hpre] at hfull
      simp at hfull
  | some p =>
      have hbound :=
        BB429ZeroRegularHeadMax.junc0_regular_prefix_before_old_mark
          v w t ht p hpre
      have hproj := runWithMax_toDelta t (junc 0 v (w+3))
      rw [hpre] at hproj
      have hdelta :
          runWithDelta t (junc 0 v (w+3)) = some (p.1,p.2.1) := by
        simpa using hproj.symm
      obtain ⟨d,hraw,_,hhead⟩ :=
        source_runWithDelta_rep t (junc 0 v (w+3)) c hrep
          p.1 p.2.1 hdelta
      refine ⟨d,hraw,?_⟩
      omega

/-- During any ordinary positive-u Junc return, every original-machine
primitive head position lies to the left of the starting last right mark. -/
theorem physical_positive_regular_all_prefixes_before_old_mark
    (u v w t : Nat) (c : Config)
    (hrep : Represents (junc (u+1) v (w+2)) c) (ht : t ≤ 4*v+10) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      d.head < c.head + ((2*v+w+5 : Nat) : Int) := by
  have hfull := BB429PositiveRegularHeadMax.juncPos_ordinary_max u v w
  have hlen : 4*v+10 = t+(4*v+10-t) := by omega
  cases hpre : runWithMax t (junc (u+1) v (w+2)) with
  | none =>
      rw [hlen,runWithMax_add,hpre] at hfull
      simp at hfull
  | some p =>
      have hbound :=
        BB429PositiveRegularHeadMax.juncPos_ordinary_prefix_before_old_mark
          u v w t ht p hpre
      have hproj := runWithMax_toDelta t (junc (u+1) v (w+2))
      rw [hpre] at hproj
      have hdelta :
          runWithDelta t (junc (u+1) v (w+2)) = some (p.1,p.2.1) := by
        simpa using hproj.symm
      obtain ⟨d,hraw,_,hhead⟩ :=
        source_runWithDelta_rep t (junc (u+1) v (w+2)) c hrep
          p.1 p.2.1 hdelta
      refine ⟨d,hraw,?_⟩
      omega

/-- The physical absolute coordinate of the furthest right source mark
is conserved across every ordinary zero-u Junc return. -/
theorem physical_zero_regular_frontier_conserved
    (v w : Nat) (c : Config)
    (hrep : Represents (junc 0 v (w+3)) c) :
    ∃ d, BB6Coverage.run target429 (2*v+27) c = some d ∧
      Represents (junc (v+3) 0 w) d ∧
      d.head + ((w+3 : Nat) : Int) =
        c.head + ((2*v+w+6 : Nat) : Int) := by
  have hmax := BB429ZeroRegularHeadMax.junc0_regular_max v w
  have hproj := runWithMax_toDelta (2*v+27) (junc 0 v (w+3))
  rw [hmax] at hproj
  have hdelta : runWithDelta (2*v+27) (junc 0 v (w+3)) =
      some (junc (v+3) 0 w, ((2*v+3 : Nat) : Int)) := by
    simpa using hproj.symm
  obtain ⟨d,hraw,hrepd,hhead⟩ :=
    source_runWithDelta_rep (2*v+27) (junc 0 v (w+3)) c hrep
      (junc (v+3) 0 w) ((2*v+3 : Nat) : Int) hdelta
  refine ⟨d,hraw,hrepd,?_⟩
  omega

/-- The physical absolute coordinate of the furthest right source mark
is conserved across every ordinary positive-u Junc return. -/
theorem physical_positive_regular_frontier_conserved
    (u v w : Nat) (c : Config)
    (hrep : Represents (junc (u+1) v (w+2)) c) :
    ∃ d, BB6Coverage.run target429 (4*v+10) c = some d ∧
      Represents (junc u (v+2) w) d ∧
      d.head + ((2*(v+2)+w+3 : Nat) : Int) =
        c.head + ((2*v+w+5 : Nat) : Int) := by
  have hmax := BB429PositiveRegularHeadMax.juncPos_ordinary_max u v w
  have hproj := runWithMax_toDelta (4*v+10) (junc (u+1) v (w+2))
  rw [hmax] at hproj
  have hdelta : runWithDelta (4*v+10) (junc (u+1) v (w+2)) =
      some (junc u (v+2) w, -2) := by
    simpa using hproj.symm
  obtain ⟨d,hraw,hrepd,hhead⟩ :=
    source_runWithDelta_rep (4*v+10) (junc (u+1) v (w+2))
      c hrep (junc u (v+2) w) (-2) hdelta
  refine ⟨d,hraw,hrepd,?_⟩
  omega

#print axioms physical_zero_regular_all_prefixes_before_old_mark
#print axioms physical_positive_regular_all_prefixes_before_old_mark
#print axioms physical_zero_regular_frontier_conserved
#print axioms physical_positive_regular_frontier_conserved

end BB429PhysicalRegularHeadMax
