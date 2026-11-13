import Low43Physical
import W4JuncGeneral
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 32768

namespace BB429Low43UniformContinuation

open BB6Coverage BB6Bubble BB429PhysicalFrontier
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429Low43Delta BB429Low43Physical BB429DeltaPhysicalBridge
open BB429W4JuncGeneral

/-- The alternating 10-block, followed by six ones, is a leading one
    followed by the corresponding 01-block and five ones. -/
private theorem tens_even_tail (k : Nat) :
    tens (2*k) ++ ones 6 = true :: (pairs01 (2*k) ++ ones 5) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      have ht : tens (2*(k+1)) =
          true :: false :: true :: false :: tens (2*k) := by
        rw [Nat.mul_succ]
        simp [tens]
      have hp : pairs01 (2*(k+1)) =
          false :: true :: false :: true :: pairs01 (2*k) := by
        rw [Nat.mul_succ]
        simp [pairs01]
      rw [ht, hp]
      simpa [List.cons_append] using
        congrArg (fun xs => true :: false :: true :: false :: xs) ih

/-- Six original transitions turn the C/0 low43 checkpoint into an E/1
    sweep input. The untouched alternating tail is deliberately retained. -/
theorem low43_C0_six_delta (v k : Nat) :
    runWithDelta 6 (low43_C0_zipper v k) =
      some (z 4 ([true,true] ++ ones (4*v+6) ++ tens (2*k) ++ ones 6)
        true [true,false,true], -2) := by
  rfl

/-- The low43 C/0 checkpoint reaches the even source E/1 boundary in
    exactly 4v+15 steps, with displacement -(4v+11). -/
theorem low43_C0_to_sourceScanE_delta (v k : Nat) :
    runWithDelta (4*v+15) (low43_C0_zipper v k) =
      some (sourceScanE (2*k) (sourceSuffix (2*v+2)),
        -((4*v+11 : Nat) : Int)) := by
  have hfirst := low43_C0_six_delta v k
  have hprefix : [true,true] ++ ones (4*v+6) = ones (4*v+8) := by
    have h := BB429SourceE1Return.ones_add 2 (4*v+6)
    have ha : 2+(4*v+6) = 4*v+8 := by omega
    rw [ha] at h
    simpa [ones] using h.symm
  have hone : ones (4*v+8) ++ [true] = ones (4*v+9) := by
    have h := BB429SourceE1Return.ones_add (4*v+8) 1
    have ha : (4*v+8)+1 = 4*v+9 := by omega
    rw [ha] at h
    simpa [ones] using h.symm
  have hleft :
      [true,true] ++ (ones (4*v+6) ++ (tens (2*k) ++ ones 6)) =
        ones (4*v+9) ++ (pairs01 (2*k) ++ ones 5) := by
    calc
      [true,true] ++ (ones (4*v+6) ++ (tens (2*k) ++ ones 6)) =
          ([true,true] ++ ones (4*v+6)) ++ (tens (2*k) ++ ones 6) := by
            rw [← List.append_assoc]
      _ = ones (4*v+8) ++ (tens (2*k) ++ ones 6) := by
            rw [hprefix]
      _ = ones (4*v+8) ++ (true :: (pairs01 (2*k) ++ ones 5)) := by
            rw [tens_even_tail]
      _ = (ones (4*v+8) ++ [true]) ++
            (pairs01 (2*k) ++ ones 5) := by
            rw [← List.append_assoc]
      _ = ones (4*v+9) ++ (pairs01 (2*k) ++ ones 5) := by
            rw [hone]
  have hfirst' :
      runWithDelta 6 (low43_C0_zipper v k) =
        some (z 4 (ones (4*v+9) ++ (pairs01 (2*k) ++ ones 5))
          true [true,false,true], -2) := by
    simpa only [hleft] using hfirst
  have hSweep :=
    BB429W4JuncGeneral.E1_sweep_prefix_delta
      (4*v+9) (pairs01 (2*k) ++ ones 5) [true,false,true]
  have h1 : ones (4*v+9) ++ [true] = ones (4*v+10) := by
    have h := BB429SourceE1Return.ones_add (4*v+9) 1
    have ha : (4*v+9)+1 = 4*v+10 := by omega
    rw [ha] at h
    simpa [ones] using h.symm
  have h2 : ones 6 ++ ones (4*v+4) = ones (4*v+10) := by
    have h := BB429SourceE1Return.ones_add 6 (4*v+4)
    have ha : 6+(4*v+4) = 4*v+10 := by omega
    rw [ha] at h
    exact h.symm
  have hright :
      ones (4*v+9) ++ [true,false,true] =
        sourceSuffix (2*v+2) := by
    unfold sourceSuffix
    rw [show 2*(2*v+2) = 4*v+4 by omega]
    calc
      ones (4*v+9) ++ [true,false,true] =
          (ones (4*v+9) ++ [true]) ++ [false,true] := by
            simp [List.append_assoc]
      _ = ones (4*v+10) ++ [false,true] := by rw [h1]
      _ = (ones 6 ++ ones (4*v+4)) ++ [false,true] := by rw [← h2]
      _ = ones 6 ++ ones (4*v+4) ++ [false,true] := by
            rw [List.append_assoc]
  have hcfg :
      z 4 (pairs01 (2*k) ++ ones 5) true
          (ones (4*v+9) ++ [true,false,true]) =
        sourceScanE (2*k) (sourceSuffix (2*v+2)) := by
    simp [sourceScanE, hright]
  have htime : 4*v+15 = 6+(4*v+9) := by omega
  rw [htime, runWithDelta_add, hfirst']
  simp only [Option.bind_some]
  rw [hSweep]
  simp only [Option.map_some]
  rw [hcfg]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

/-- Uniform low43 C/0 continuation: for every v>=1 and k>=0, the
    original six-state source reaches Junc(2k+9,0,4v-2) in
    38k+4v+152 primitive transitions. -/
theorem low43_C0_to_junc_delta (v k : Nat) (hv : 1 ≤ v) :
    runWithDelta (38*k+4*v+152) (low43_C0_zipper v k) =
      some (junc (2*k+9) 0 (4*v-2), -((4*v : Nat) : Int)) := by
  have hentry := low43_C0_to_sourceScanE_delta v k
  have hscanTime :
      18*k+54 = crossTime (2*k)+1+(12+2*(2*k)) := by
    rw [BB429SourceE1Return.crossTime_even]
    omega
  have hscan : runWithDelta (18*k+54)
      (sourceScanE (2*k) (sourceSuffix (2*v+2))) =
      some (junc 2 (2*k+2) (4*v+5), -((4*k : Nat) : Int)) := by
    rw [hscanTime]
    have h := sourceScanE_finishC_even_delta k (2*v+2)
    simpa [show 2*(2*v+2)+1 = 4*v+5 by omega,
      show 2*(2*k) = 4*k by omega] using h
  have hposTime : 16*k+44 = juncPosFullTime 2 (2*k+2) := by
    simp [juncPosFullTime]
    omega
  have hpos : runWithDelta (16*k+44)
      (junc 2 (2*k+2) (4*v+5)) =
      some (junc 0 (2*k+6) (4*v+1), -4) := by
    rw [hposTime]
    have h := juncPos_iter_full_delta 2 2 (2*k+2) (4*v+5)
      (by omega) (by omega)
    have hU : 2-2 = 0 := by omega
    have hV : 2*k+2+2*2 = 2*k+6 := by omega
    have hW : 4*v+5-2*2 = 4*v+1 := by omega
    simpa [hU, hV, hW] using h
  have hnormTime :
      4*k+39 = juncNormalizeTime 0 (2*k+6) := by
    simp [juncNormalizeTime, juncPosFullTime]
    omega
  have hnorm : runWithDelta (4*k+39)
      (junc 0 (2*k+6) (4*v+1)) =
      some (junc (2*k+9) 0 (4*v-2), ((4*k+15 : Nat) : Int)) := by
    rw [hnormTime]
    have h := juncNormalize_delta 0 (2*k+6) (4*v+1) (by omega)
    have hU : 2*k+6+2*0+3 = 2*k+9 := by omega
    have hW : 4*v+1-(2*0+3) = 4*v-2 := by omega
    have hd : 2*(2*k+6)+2*0+3 = 4*k+15 := by omega
    simpa [hU, hW, hd] using h
  have htime :
      38*k+4*v+152 =
        (4*v+15)+((18*k+54)+((16*k+44)+(4*k+39))) := by omega
  rw [htime, runWithDelta_add, hentry]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hscan]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hpos]
  simp only [Option.bind_some]
  rw [hnorm]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

/-- Physical lift of the uniform source continuation, preserving the
    exact original transition table and head displacement. -/
theorem physical_low43_C0_to_junc (v k : Nat) (hv : 1 ≤ v)
    (c : Config) (hrep : Represents (low43_C0_zipper v k) c) :
    ∃ c', run target429 (38*k+4*v+152) c = some c' ∧
      Represents (junc (2*k+9) 0 (4*v-2)) c' ∧
      c'.head = c.head - (4*v : Int) := by
  obtain ⟨c', hrun, hrep', hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (38*k+4*v+152) (low43_C0_zipper v k) c hrep
      (junc (2*k+9) 0 (4*v-2)) (-(4*v : Int))
      (low43_C0_to_junc_delta v k hv)
  exact ⟨c', hrun, hrep', by omega⟩

#print axioms low43_C0_six_delta
#print axioms low43_C0_to_sourceScanE_delta
#print axioms low43_C0_to_junc_delta
#print axioms physical_low43_C0_to_junc

end BB429Low43UniformContinuation
