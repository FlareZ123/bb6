import OuterSafe
import LowEven4kDelta
import PhysicalNoFatalConverse
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Junc11Return32

open BB6Coverage
open BB429OddExcursion BB429JuncHeadExcursion BB429SourceE1Delta
open BB429PhysicalFrontier BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429PhysicalNoFatalConverse
open BB429OuterSafe BB429LowEven4k

/-- Compose two exact source displacement traces. -/
private theorem compose_delta {m n : Nat} {z z₁ z₂ : Zipper}
    {d e : Int}
    (h₁ : runWithDelta m z = some (z₁, d))
    (h₂ : runWithDelta n z₁ = some (z₂, e)) :
    runWithDelta (m+n) z = some (z₂, d+e) := by
  rw [runWithDelta_add m n z, h₁]
  simp only [Option.bind_some]
  rw [h₂]
  simp only [Option.map_some]

/-- The closed form for the positive-u Junc iteration time. -/
private theorem juncPosFullTime_formula (N v : Nat) :
    juncPosFullTime N v = 4*N*N + (4*v+6)*N := by
  induction N generalizing v with
  | zero => simp [juncPosFullTime]
  | succ N ih =>
      simp [juncPosFullTime, ih]
      omega

/-- One complete outer-safe Junc return, now with its exact head
    displacement. The positive-u sweep moves left by 2U, and the final
    regular zero-u return moves right by 2(v+2U)+3. -/
private theorem outer_delta (U v w : Nat) (hw : 2*U+3 ≤ w) :
    runWithDelta (outerCost U v) (junc U v w) =
      some (junc (v+2*U+3) 0 (w-(2*U+3)),
        ((2*v+2*U+3 : Nat) : Int)) := by
  have hpos :
      runWithDelta (juncPosFullTime U v) (junc U v w) =
        some (junc 0 (v+2*U) (w-2*U), -((2*U : Nat) : Int)) := by
    simpa using
      (juncPos_iter_full_delta U U v w (by omega) (by omega))
  have hzero :
      runWithDelta (2*(v+2*U)+27) (junc 0 (v+2*U) (w-2*U)) =
        some (junc (v+2*U+3) 0 ((w-2*U)-3),
          ((2*(v+2*U)+3 : Nat) : Int)) :=
    junc0_next_delta (v+2*U) (w-2*U) (by omega)
  have hcomp := compose_delta hpos hzero
  have hwidth : (w-2*U)-3 = w-(2*U+3) := by omega
  have hdisp :
      -((2*U : Nat) : Int) + ((2*(v+2*U)+3 : Nat) : Int) =
        ((2*v+2*U+3 : Nat) : Int) := by omega
  simpa [outerCost, hwidth, hdisp] using hcomp

/-- Lift one outer return to any complete physical tape representing its
    Junc input, retaining the exact endpoint and absolute head shift. -/
theorem outer_segment_physical_delta
    (U v w : Nat) (c : Config)
    (hrep : Represents (junc U v w) c)
    (hw : 2*U+3 ≤ w) :
    ∃ d : Config,
      run target429 (outerCost U v) c = some d ∧
      Represents (junc (v+2*U+3) 0 (w-(2*U+3))) d ∧
      d.head = c.head + ((2*v+2*U+3 : Nat) : Int) := by
  obtain ⟨d, hraw, hrepD, hhead⟩ :=
    source_runWithDelta_rep (outerCost U v) (junc U v w) c hrep
      (junc (v+2*U+3) 0 (w-(2*U+3)))
      ((2*v+2*U+3 : Nat) : Int)
      (outer_delta U v w hw)
  exact ⟨d, hraw, hrepD, hhead⟩

/-- The four outer-safe reductions 11 -> 25 -> 53 -> 109 -> 221
    take 63,832 steps, move the head right by 408, and consume 408
    units of the right budget. -/
private theorem outer4_delta (N : Nat) :
    runWithDelta 63832 (junc 11 0 (408+2*N)) =
      some (junc 221 0 (2*N), (408 : Int)) := by
  let w₀ := 408+2*N
  let w₁ := w₀-25
  let w₂ := w₁-53
  let w₃ := w₂-109
  let w₄ := w₃-221
  have h₁ : runWithDelta (outerCost 11 0) (junc 11 0 w₀) =
      some (junc 25 0 w₁, (25 : Int)) := by
    have h := outer_delta 11 0 w₀ (by dsimp [w₀]; omega)
    simpa [w₁] using h
  have h₂ : runWithDelta (outerCost 25 0) (junc 25 0 w₁) =
      some (junc 53 0 w₂, (53 : Int)) := by
    have h := outer_delta 25 0 w₁ (by dsimp [w₁,w₀]; omega)
    simpa [w₂] using h
  have h₃ : runWithDelta (outerCost 53 0) (junc 53 0 w₂) =
      some (junc 109 0 w₃, (109 : Int)) := by
    have h := outer_delta 53 0 w₂ (by dsimp [w₂,w₁,w₀]; omega)
    simpa [w₃] using h
  have h₄ : runWithDelta (outerCost 109 0) (junc 109 0 w₃) =
      some (junc 221 0 w₄, (221 : Int)) := by
    have h := outer_delta 109 0 w₃ (by dsimp [w₃,w₂,w₁,w₀]; omega)
    simpa [w₄] using h
  have h₁₂ := compose_delta h₁ h₂
  have h₁₂₃ := compose_delta h₁₂ h₃
  have h₁₂₃₄ := compose_delta h₁₂₃ h₄
  have htime :
      ((outerCost 11 0 + outerCost 25 0) + outerCost 53 0) +
        outerCost 109 0 = 63832 := by
    norm_num [outerCost, juncPosFullTime_formula]
  have hwidth : w₄ = 2*N := by
    dsimp [w₀,w₁,w₂,w₃,w₄]
    omega
  have hdisp :
      ((25 : Int) + 53) + 109 + 221 = 408 := by norm_num
  simpa [htime, hwidth, hdisp] using h₁₂₃₄

/-- Physical form of the four-step outer reduction. -/
private theorem outer4_physical
    (N : Nat) (c : Config)
    (hrep : Represents (junc 11 0 (408+2*N)) c) :
    ∃ d : Config,
      run target429 63832 c = some d ∧
      Represents (junc 221 0 (2*N)) d ∧
      d.head = c.head + 408 := by
  obtain ⟨d, hraw, hrepD, hhead⟩ :=
    source_runWithDelta_rep 63832 (junc 11 0 (408+2*N)) c hrep
      (junc 221 0 (2*N)) 408 (outer4_delta N)
  exact ⟨d, hraw, hrepD, hhead⟩

/-- Exact primitive cost of the four-outer-step / low-even-4k return. -/
def junc11Return32Cost (N K : Nat) : Nat :=
  64093 + 4*N*N + 22*N + 18*K

/-- For N+2K=221, four outer-safe returns followed by the parameterized
    low-even 4k macro take J(11,408+2N) to J(11,440+2N). The endpoint
    width grows by 32 and the physical head moves left by exactly 25. -/
theorem junc11_lowEven_return32_physical
    (N K : Nat) (hNK : N+2*K=221) (hK : 1 ≤ K)
    (c : Config)
    (hrep : Represents (junc 11 0 (408+2*N)) c) :
    ∃ d : Config,
      run target429 (junc11Return32Cost N K) c = some d ∧
      Represents (junc 11 0 (440+2*N)) d ∧
      d.head = c.head - 25 := by
  obtain ⟨c₂₂₁, houter, hrep₂₂₁, hheadOuter⟩ :=
    outer4_physical N c hrep
  have hrep₂₂₁' : Represents (junc (N+2*K) 0 (2*N)) c₂₂₁ := by
    simpa [hNK] using hrep₂₂₁
  obtain ⟨d, hlow, hrepD, hheadLow⟩ :=
    lowEven4k_prepared_return_physical N K hK c₂₂₁ hrep₂₂₁'
  have hrun :=
    physical_run_add_of_endpoint 63832
      (juncPosFullTime N 0 + (16*N+18*K+261))
      c c₂₂₁ d houter hlow
  have htime :
      63832 + (juncPosFullTime N 0 + (16*N+18*K+261)) =
        junc11Return32Cost N K := by
    simp [junc11Return32Cost, juncPosFullTime_formula]
    omega
  have hwidth : 4*N+4*K-2 = 440+2*N := by omega
  have hhead : d.head = c.head - 25 := by
    rw [hheadLow, hheadOuter]
    omega
  exact ⟨d, by simpa [htime] using hrun,
    by simpa [hwidth] using hrepD, hhead⟩

#print axioms outer_delta
#print axioms outer4_delta
#print axioms junc11_lowEven_return32_physical

end BB429Junc11Return32
