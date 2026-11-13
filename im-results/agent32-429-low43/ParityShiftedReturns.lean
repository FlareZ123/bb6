import BB429JuncHeadExcursion
import MidAposBoundary
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429ParityShiftedReturns

open BB6Coverage
open BB429FinishScanEDelta
open BB429W4HeadMax
open BB429JuncHeadExcursion
open BB429MidAposBoundary

/-- Compose two exact source-level runWithDelta segments. -/
theorem compose_runWithDelta
    {n m : Nat} {z₀ z₁ z₂ : Zipper} {d₁ d₂ : Int}
    (h₁ : runWithDelta n z₀ = some (z₁, d₁))
    (h₂ : runWithDelta m z₁ = some (z₂, d₂)) :
    runWithDelta (n + m) z₀ = some (z₂, d₁ + d₂) := by
  rw [runWithDelta_add, h₁]
  simp [h₂]

/-- The shifted C/0 zipper observed from J(93,0,173) at step 31,154. -/
def parityShiftedC0 : Zipper :=
  z 2 (true :: false :: (ones 353 ++ pairs01 4 ++ [false] ++ ones 6)) false []

/-- Concrete 425-step C/0 continuation to J(0,7,349). -/
theorem parityShiftedC0_to_junc07 :
    runWithDelta 425 parityShiftedC0 =
      some (junc 0 7 349, -365) := by
  decide

/-- The even-u w=1 MidA instance needed at J(15,172,1). -/
theorem midApos_14_172_1_to_junc0 :
    runWithDelta 1201 (midApos 14 172 1) =
      some (junc 0 15 349, -377) := by
  decide

/-- The even-u w=1 MidA instance needed at J(135,60,1). -/
theorem midApos_134_60_1_to_junc0 :
    runWithDelta 1609 (midApos 134 60 1) =
      some (junc 0 135 125, -393) := by
  decide

/-- The remaining A/0 suffix after the existing w=2 MidA exit. -/
theorem midApos_77_120_2_A0_suffix :
    runWithDelta 1489
      (z 0 (ones (2 * 120 + 9) ++ pairs01 (77 - 1) ++ ones 5) false [true]) =
      some (junc 0 0 408, -403) := by
  decide

/-- Exact return J(15,172,1) -> J(0,15,349), split at MidApos. -/
theorem junc15_172_1_to_junc0_15_349 :
    runWithDelta 1551 (junc 15 172 1) =
      some (junc 0 15 349, -31) := by
  have h₁ := juncPos_to_midA_delta 14 172 1 (by omega)
  have h₂ := midApos_14_172_1_to_junc0
  have h := compose_runWithDelta h₁ h₂
  norm_num at h
  exact h

/-- Exact return J(135,60,1) -> J(0,135,125), split at MidApos. -/
theorem junc135_60_1_to_junc0_135_125 :
    runWithDelta 1735 (junc 135 60 1) =
      some (junc 0 135 125, -271) := by
  have h₁ := juncPos_to_midA_delta 134 60 1 (by omega)
  have h₂ := midApos_134_60_1_to_junc0
  have h := compose_runWithDelta h₁ h₂
  norm_num at h
  exact h

/-- Exact return J(78,120,2) -> J(0,0,408), split at the w=2 MidA exit. -/
theorem junc78_120_2_to_junc0_0_408 :
    runWithDelta 2229 (junc 78 120 2) =
      some (junc 0 0 408, -159) := by
  have h₁ := juncPos_to_midA_delta 77 120 2 (by omega)
  have h₂ := midApos_w2_exit_delta 77 120 (by omega)
  have h₃ := midApos_77_120_2_A0_suffix
  have h₁₂ := compose_runWithDelta h₁ h₂
  have h := compose_runWithDelta h₁₂ h₃
  norm_num at h
  exact h

/-- Full source-level 102,656-step continuation from J(0,7,349) to J(0,0,408). -/
theorem junc07_349_to_junc0_408 :
    runWithDelta 102656 (junc 0 7 349) =
      some (junc 0 0 408, -32) := by
  have step1 : runWithDelta (juncNormalizeTime 0 7) (junc 0 7 349) =
      some (junc 10 0 346, 17) := by
    simpa using juncNormalize_delta 0 7 349 (by omega)
  have step2 : runWithDelta (juncNormalizeTime 10 0) (junc 10 0 346) =
      some (junc 23 0 323, 23) := by
    simpa using juncNormalize_delta 10 0 346 (by omega)
  have step3 : runWithDelta (juncNormalizeTime 23 0) (junc 23 0 323) =
      some (junc 49 0 274, 49) := by
    simpa using juncNormalize_delta 23 0 323 (by omega)
  have step4 : runWithDelta (juncNormalizeTime 49 0) (junc 49 0 274) =
      some (junc 101 0 173, 101) := by
    simpa using juncNormalize_delta 49 0 274 (by omega)
  have step5 : runWithDelta (juncPosFullTime 86 0) (junc 101 0 173) =
      some (junc 15 172 1, -172) := by
    simpa using juncPos_iter_full_delta 86 101 0 173 (by omega) (by omega)
  have step6 := junc15_172_1_to_junc0_15_349
  have step7 : runWithDelta (juncNormalizeTime 0 15) (junc 0 15 349) =
      some (junc 18 0 346, 33) := by
    simpa using juncNormalize_delta 0 15 349 (by omega)
  have step8 : runWithDelta (juncNormalizeTime 18 0) (junc 18 0 346) =
      some (junc 39 0 307, 39) := by
    simpa using juncNormalize_delta 18 0 346 (by omega)
  have step9 : runWithDelta (juncNormalizeTime 39 0) (junc 39 0 307) =
      some (junc 81 0 226, 81) := by
    simpa using juncNormalize_delta 39 0 307 (by omega)
  have step1₀ : runWithDelta (juncNormalizeTime 81 0) (junc 81 0 226) =
      some (junc 165 0 61, 165) := by
    simpa using juncNormalize_delta 81 0 226 (by omega)
  have step1₁ : runWithDelta (juncPosFullTime 30 0) (junc 165 0 61) =
      some (junc 135 60 1, -60) := by
    simpa using juncPos_iter_full_delta 30 165 0 61 (by omega) (by omega)
  have step1₂ := junc135_60_1_to_junc0_135_125
  have step1₃ : runWithDelta (juncNormalizeTime 0 135) (junc 0 135 125) =
      some (junc 138 0 122, 273) := by
    simpa using juncNormalize_delta 0 135 125 (by omega)
  have step1₄ : runWithDelta (juncPosFullTime 60 0) (junc 138 0 122) =
      some (junc 78 120 2, -120) := by
    simpa using juncPos_iter_full_delta 60 138 0 122 (by omega) (by omega)
  have step1₅ := junc78_120_2_to_junc0_0_408

  have chain2 := compose_runWithDelta step1 step2
  have chain3 := compose_runWithDelta chain2 step3
  have chain4 := compose_runWithDelta chain3 step4
  have chain5 := compose_runWithDelta chain4 step5
  have chain6 := compose_runWithDelta chain5 step6
  have chain7 := compose_runWithDelta chain6 step7
  have chain8 := compose_runWithDelta chain7 step8
  have chain9 := compose_runWithDelta chain8 step9
  have chain10 := compose_runWithDelta chain9 step10
  have chain11 := compose_runWithDelta chain10 step11
  have chain12 := compose_runWithDelta chain11 step12
  have chain13 := compose_runWithDelta chain12 step13
  have chain14 := compose_runWithDelta chain13 step14
  have chain15 := compose_runWithDelta chain14 step15
  norm_num [juncNormalizeTime, juncPosFullTime] at chain15
  exact chain15

/-- Complete source-level continuation from the shifted C/0 zipper to J(0,0,408). -/
theorem parityShiftedC0_to_junc0_408 :
    runWithDelta 103081 parityShiftedC0 =
      some (junc 0 0 408, -397) := by
  have h := compose_runWithDelta parityShiftedC0_to_junc07 junc07_349_to_junc0_408
  norm_num at h
  exact h

#print axioms parityShiftedC0_to_junc07
#print axioms midApos_14_172_1_to_junc0
#print axioms midApos_134_60_1_to_junc0
#print axioms midApos_77_120_2_A0_suffix
#print axioms junc15_172_1_to_junc0_15_349
#print axioms junc135_60_1_to_junc0_135_125
#print axioms junc78_120_2_to_junc0_0_408
#print axioms junc07_349_to_junc0_408
#print axioms parityShiftedC0_to_junc0_408

end BB429ParityShiftedReturns
