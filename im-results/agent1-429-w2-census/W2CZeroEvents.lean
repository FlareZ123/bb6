import W2JuncFullCount
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2CZeroEvents

open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429W4CZeroSafe BB429W4CZeroCount BB429High2Tail BB429JuncHeadExcursion
open BB429W2MidAauxCount BB429W4CZeroOrdinary BB429W2JuncFullCount

/-- The unique C/0 in the base A/F residual occurs at a precise
    primitive time, with its entire right half-tape blank.
    The successful guarded execution rules out every earlier C/0. -/
theorem midAaux_zero_gate_safe (k : Nat) :
    runSafe (2*k+8) (midAaux 0 k) =
      some (z 2 (true::false::ones (2*k+10)) false []) := by
  have h0 : runSafe 4 (midAaux 0 k) =
      some (z 0 (ones 8) false (tens k ++ [false,true])) := by rfl
  have h1 := a_right_pairs_safe k (ones 8) [false,true]
  have hsum : ones (2*k) ++ ones 8 = ones (2*k+8) := by
    rw [show 2*k+8=2*k+8 by omega,BB429FinishScanEDelta.ones_add]
  have h2 : runSafe 2 (z 0 (ones (2*k+8)) false [false,true]) =
      some (z 2 (ones (2*k+10)) true []) := by
    have hleft : ones (2*k+10) = true::true::ones (2*k+8) := by
      rw [show 2*k+10=2+(2*k+8) by omega,BB429FinishScanEDelta.ones_add]
      rfl
    rw [hleft]; rfl
  have h3 : runSafe 2 (z 2 (ones (2*k+10)) true []) =
      some (z 2 (true::false::ones (2*k+10)) false []) := by rfl
  rw [show 2*k+8=4+(2*k+(2+2)) by omega,runSafe_add,h0]
  simp only [Option.bind_some]
  rw [runSafe_add,h1]
  simp only [Option.bind_some]
  rw [hsum,runSafe_add,h2]
  simp only [Option.bind_some]
  exact h3

/-- Exact guarded first C/0 in every positive-v A/F residual. -/
theorem midAaux_all_gate_safe (v k : Nat) :
    runSafe (2*v+(2*(k+v)+8)) (midAaux v k) =
      some (z 2 (true::false::ones (2*(k+v)+10)) false []) := by
  rw [runSafe_add,midAaux_reduce_safe]
  simp only [Option.bind_some]
  exact midAaux_zero_gate_safe (k+v)

/-- The MidA right-one passage reaches its only C/0 with no right marks. -/
theorem midApos_w1_gate_safe (v : Nat) (hv : 1 ≤ v) :
    runSafe (4*v+16) (midApos 1 v 1) =
      some (z 2 (true::false::ones (2*v+14)) false []) := by
  have hsub : v-1+1=v := Nat.sub_add_cancel hv
  have hfirst : runSafe 6 (midApos 1 v 1) = some (midAaux (v-1) 3) := by
    simpa [hsub] using midApos_to_midAaux_safe (v-1)
  have hlast := midAaux_all_gate_safe (v-1) 3
  have htime : 4*v+16 = 6 + (2*(v-1) + (2*(3+(v-1))+8)) := by omega
  rw [htime,runSafe_add,hfirst]
  simp only [Option.bind_some]
  rw [hlast]
  have hparam : 2*(3+(v-1))+10 = 2*v+14 := by omega
  rw [hparam]

/-- The complete Junc(2,v,1) return has exactly one C/0, as proved
    by junc2_w1_count; this lemma locates it at 6v+22, with blank right. -/
theorem junc2_w1_gate_safe (v : Nat) (hv : 1 ≤ v) :
    runSafe (6*v+22) (junc 2 v 1) =
      some (z 2 (true::false::ones (2*v+14)) false []) := by
  have hpre := juncPos_to_midA_safe 1 v 1 (by omega)
  have hlast := midApos_w1_gate_safe v hv
  rw [show 6*v+22 = (2*v+6)+(4*v+16) by omega,
      runSafe_add,hpre]
  simp only [Option.bind_some]
  exact hlast

/-- For all even indices v=2k+2, the SECOND C/0 occurs at the
    exact original-table time 34k+198. Its entire right half-tape is
    blank. The endpoint is excluded from the count of one prior C/0. -/
theorem junc0_w2_even_second_gate_count (k : Nat) :
    runCount (34*k+198) (junc 0 (2*k+2) 2) =
      some (z 2 (true::false::ones (4*k+26)) false [],1) := by
  have hpre : runCount (4*k+31) (junc 0 (2*k+2) 2) =
      some (z 0 (true :: (pairs01 (2*k+5) ++ ones 5)) true [false,true],0) := by
    have hp := runSafe_to_count_zero (2*(2*k+2)+27) (junc 0 (2*k+2) 2)
      (z 0 (true :: (pairs01 ((2*k+2)+3) ++ ones 5)) true [false,true])
      (junc0_w2_to_boundary_safe (2*k+2))
    simpa only [show 2*(2*k+2)+27 = 4*k+31 by omega,
      show (2*k+2)+3 = 2*k+5 by omega] using hp
  have hb := boundary_to_scanE_count (2*k)
  have hE := runSafe_to_count_zero (crossTime (2*k+4)+1)
      (sourceScanE (2*k+4) (sourceSuffix 0))
      (z 2 (finalLeft (2*k+4)) true (sourceSuffix 0))
      (scanE_safe (2*k+4) (sourceSuffix 0))
  have hentry : z 2 (finalLeft (2*k+4)) true (sourceSuffix 0) =
      finishCStart 2 (2*k+4) 0 := by
    simpa only [show 2*(k+2)=2*k+4 by omega] using
      (finalLeft_even_finishC_entry (k+2) 0)
  have hfinish := runSafe_to_count_zero (12+2*(2*k+4))
      (finishCStart 2 (2*k+4) 0) (junc 2 ((2*k+4)+2) 1)
      (finishC_ScanE_safe 2 (2*k+4) 0)
  have hg := runSafe_to_count_zero (6*(2*k+6)+22)
      (junc 2 (2*k+6) 1)
      (z 2 (true::false::ones (2*(2*k+6)+14)) false [])
      (junc2_w1_gate_safe (2*k+6) (by omega))
  have htime : 34*k+198 = (4*k+31) +
      (19 + ((crossTime (2*k+4)+1) +
        ((12+2*(2*k+4))+(6*(2*k+6)+22)))) := by
    rw [show 2*k+4=2*(k+2) by omega,crossTime_even]
    omega
  rw [htime,runCount_add,hpre]
  simp only [Option.bind_some]
  rw [runCount_add,hb]
  simp only [Option.bind_some]
  rw [runCount_add,hE]
  simp only [Option.bind_some]
  rw [hentry,runCount_add,hfinish]
  simp only [Option.bind_some]
  rw [show 2*k+4+2=2*k+6 by omega,hg]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  have hend : 2*(2*k+6)+14=4*k+26 := by omega
  rw [hend]
  trivial

#print axioms junc0_w2_even_second_gate_count

#print axioms midAaux_zero_gate_safe
#print axioms midAaux_all_gate_safe
#print axioms midApos_w1_gate_safe
#print axioms junc2_w1_gate_safe

end BB429W2CZeroEvents
