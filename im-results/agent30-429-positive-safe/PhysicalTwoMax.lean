import ZeroTwoMax
import PhysicalSafe
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429PhysicalZeroTwoMax

open BB6Coverage BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429PhysicalFrontier BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4HeadPrefix BB429ZeroTwoMax

/-- The original six-state machine's physical head stays no farther
    right than the first C/0 record head, at *every* primitive prefix
    starting from any physical tape representing junc 0 v 2. -/
theorem physical_zero_two_all_prefixes_head_bound
    (v t : Nat) (c : Config)
    (hrep : Represents (junc 0 v 2) c)
    (ht : t ≤ 2*v+35) :
    ∃ d, BB6Coverage.run target429 t c = some d ∧
      d.head ≤ c.head + ((2*v+7 : Nat) : Int) := by
  have hfull := junc0_w2_first_czero_max v
  have hlen : 2*v+35 = t+(2*v+35-t) := by omega
  cases hpre : runWithMax t (junc 0 v 2) with
  | none =>
      rw [hlen,runWithMax_add,hpre] at hfull
      simp at hfull
  | some p =>
      have hbound :=
        junc0_w2_all_prefixes_le_first_gate v t ht p hpre
      have hproj := runWithMax_toDelta t (junc 0 v 2)
      rw [hpre] at hproj
      have hdelta :
          runWithDelta t (junc 0 v 2) = some (p.1,p.2.1) := by
        simpa using hproj.symm
      obtain ⟨d,hraw,_,hhead⟩ :=
        source_runWithDelta_rep t (junc 0 v 2) c hrep
          p.1 p.2.1 hdelta
      refine ⟨d,hraw,?_⟩
      omega

/-- The very first C/0 in the exceptional right-two segment is reached
    at exact original-machine displacement +(2v+7) relative to the
    represented Junc input head. -/
theorem physical_zero_two_first_czero_exact_head
    (v : Nat) (c : Config)
    (hrep : Represents (junc 0 v 2) c) :
    ∃ d, BB6Coverage.run target429 (2*v+35) c = some d ∧
      d.state.val = 2 ∧ d.tape d.head = false ∧
      d.tape (d.head+1) = false ∧
      d.head = c.head + ((2*v+7 : Nat) : Int) := by
  have hmax := junc0_w2_first_czero_max v
  have hproj := runWithMax_toDelta (2*v+35) (junc 0 v 2)
  rw [hmax] at hproj
  have hrun :
      runWithDelta (2*v+35) (junc 0 v 2) =
        some (z 2 (([true,false] ++ ones 5) ++
          (pairs01 (v+2) ++ ones 5)) false [],
          ((2*v+7 : Nat) : Int)) := by
    simpa using hproj.symm
  obtain ⟨d,hraw,hrepd,hhead⟩ :=
    source_runWithDelta_rep (2*v+35) (junc 0 v 2)
      c hrep
      (z 2 (([true,false] ++ ones 5) ++
        (pairs01 (v+2) ++ ones 5)) false [])
      ((2*v+7 : Nat) : Int) hrun
  refine ⟨d,hraw,hrepd.1,hrepd.2.1,?_,hhead⟩
  have hr := hrepd.2.2.2 0
  change d.tape (d.head+1) = false at hr
  exact hr

#print axioms physical_zero_two_all_prefixes_head_bound
#print axioms physical_zero_two_first_czero_exact_head

end BB429PhysicalZeroTwoMax
