import OuterSafe
import Low42PhysicalNoFatalAnyHead
import PhysicalNoFatalConverse
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Junc0ReturnMap28

open BB6Coverage BB6Bubble
open BB429OddExcursion BB429FinishScanEDelta
open BB429PhysicalFrontier BB429PhysicalBridge
open BB429W4CZeroSafe BB429PositiveSafe BB429OuterSafe
open BB429PhysicalNoFatalConverse
open BB429Low42PhysicalNoFatal BB429Low42PhysicalNoFatalAnyHead

/-- Lift one exact outer-safe source return to any represented physical
    Junc input, retaining its exact endpoint representation. -/
private theorem outer_segment_physical
    (U v w : Nat) (c : Config)
    (hrep : Represents (junc U v w) c)
    (hw : 2*U+3 ≤ w) :
    ∃ d : Config,
      run target429 (outerCost U v) c = some d ∧
      Represents (junc (v+2*U+3) 0 (w-(2*U+3))) d := by
  have hsafe :
      runSafe (outerCost U v) (junc U v w) =
        some (junc (v+2*U+3) 0 ((w-2*U)-3)) :=
    junc_outer_safe U v w hw
  have hsource :
      BB429OddExcursion.run (outerCost U v) (junc U v w) =
        some (junc (v+2*U+3) 0 ((w-2*U)-3)) :=
    runSafe_to_run (outerCost U v) (junc U v w)
      (junc (v+2*U+3) 0 ((w-2*U)-3)) hsafe
  obtain ⟨d, hraw, hrepD⟩ :=
    source_run_rep (outerCost U v) (junc U v w) c hrep
      (junc (v+2*U+3) 0 ((w-2*U)-3)) hsource
  have hwidth : ((w-2*U)-3) = w-(2*U+3) := by omega
  exact ⟨d, hraw, by simpa [hwidth] using hrepD⟩

/-- Six outer-safe returns reduce Junc(0,0,4(r+90)) to
    Junc(189,0,4r), for 12 <= r <= 94. -/
private theorem outer_ladder_physical
    (r : Nat) (hrlo : 12 ≤ r) (hrhi : r ≤ 94)
    (c : Config)
    (hrep : Represents (junc 0 0 (4*(r+90))) c) :
    ∃ d : Config,
      run target429 46692 c = some d ∧
      Represents (junc 189 0 (4*r)) d := by
  let w0 := 4*(r+90)
  let w1 := w0-3
  let w2 := w1-9
  let w3 := w2-21
  let w4 := w3-45
  let w5 := w4-93
  let w6 := w5-189

  obtain ⟨c1,h1,r1⟩ :=
    outer_segment_physical 0 0 w0 c hrep (by dsimp [w0]; omega)
  have r1' : Represents (junc 3 0 w1) c1 := by
    simpa [w0, w1] using r1

  obtain ⟨c2,h2,r2⟩ :=
    outer_segment_physical 3 0 w1 c1 r1' (by dsimp [w0, w1]; omega)
  have r2' : Represents (junc 9 0 w2) c2 := by
    simpa [w1, w2] using r2

  obtain ⟨c3,h3,r3⟩ :=
    outer_segment_physical 9 0 w2 c2 r2' (by dsimp [w0, w1, w2]; omega)
  have r3' : Represents (junc 21 0 w3) c3 := by
    simpa [w2, w3] using r3

  obtain ⟨c4,h4,r4⟩ :=
    outer_segment_physical 21 0 w3 c3 r3' (by dsimp [w0, w1, w2, w3]; omega)
  have r4' : Represents (junc 45 0 w4) c4 := by
    simpa [w3, w4] using r4

  obtain ⟨c5,h5,r5⟩ :=
    outer_segment_physical 45 0 w4 c4 r4' (by dsimp [w0, w1, w2, w3, w4]; omega)
  have r5' : Represents (junc 93 0 w5) c5 := by
    simpa [w4, w5] using r5

  obtain ⟨c6,h6,r6⟩ :=
    outer_segment_physical 93 0 w5 c5 r5' (by dsimp [w0, w1, w2, w3, w4, w5]; omega)
  have r6' : Represents (junc 189 0 w6) c6 := by
    simpa [w5, w6] using r6
  have hw6 : w6 = 4*r := by
    dsimp [w0, w1, w2, w3, w4, w5, w6]
    omega
  have r6'' : Represents (junc 189 0 (4*r)) c6 := by
    simpa [hw6] using r6'

  have h01 : run target429 (outerCost 0 0 + outerCost 3 0) c = some c2 :=
    physical_run_add_of_endpoint (outerCost 0 0) (outerCost 3 0)
      c c1 c2 h1 h2
  have h012 :
      run target429 (outerCost 0 0 + outerCost 3 0 + outerCost 9 0) c =
        some c3 :=
    physical_run_add_of_endpoint
      (outerCost 0 0 + outerCost 3 0) (outerCost 9 0)
      c c2 c3 h01 h3
  have h0123 :
      run target429
        (outerCost 0 0 + outerCost 3 0 + outerCost 9 0 + outerCost 21 0) c =
        some c4 :=
    physical_run_add_of_endpoint
      (outerCost 0 0 + outerCost 3 0 + outerCost 9 0) (outerCost 21 0)
      c c3 c4 h012 h4
  have h01234 :
      run target429
        (outerCost 0 0 + outerCost 3 0 + outerCost 9 0 +
          outerCost 21 0 + outerCost 45 0) c = some c5 :=
    physical_run_add_of_endpoint
      (outerCost 0 0 + outerCost 3 0 + outerCost 9 0 + outerCost 21 0)
      (outerCost 45 0) c c4 c5 h0123 h5
  have h012345 :
      run target429
        (outerCost 0 0 + outerCost 3 0 + outerCost 9 0 +
          outerCost 21 0 + outerCost 45 0 + outerCost 93 0) c = some c6 :=
    physical_run_add_of_endpoint
      (outerCost 0 0 + outerCost 3 0 + outerCost 9 0 +
        outerCost 21 0 + outerCost 45 0)
      (outerCost 93 0) c c5 c6 h01234 h6
  have htime :
      outerCost 0 0 + outerCost 3 0 + outerCost 9 0 +
        outerCost 21 0 + outerCost 45 0 + outerCost 93 0 = 46692 := by
    decide
  have houter : run target429 46692 c = some c6 := by
    simpa [htime] using h012345
  exact ⟨c6, houter, r6''⟩

/-- Uniform physical Junc(0,w) -> Junc(0,w+28) return map on the
    observed finite interval 408 <= w <= 736, with w divisible by four.
    The parameter r gives w=4(r+90), 12<=r<=94. Every primitive prefix
    is C/01-free on the original physical tape. -/
theorem junc0_return_map_28
    (r : Nat) (hrlo : 12 ≤ r) (hrhi : r ≤ 94)
    (c : Config)
    (hrep : Represents (junc 0 0 (4*(r+90))) c) :
    ∃ d : Config,
      run target429
        (46692 + (4*(2*r)*(2*r) + 22*(2*r) + 18*(94-r) + 79)) c =
          some d ∧
      Represents (junc 0 0 (4*(r+97))) d ∧
      (∀ t, t ≤ 46692 +
          (4*(2*r)*(2*r) + 22*(2*r) + 18*(94-r) + 79) →
        ∃ e : Config, run target429 t c = some e ∧
          ¬ physicalC01 e) := by
  obtain ⟨c6, houter, hrep6⟩ :=
    outer_ladder_physical r hrlo hrhi c hrep
  have hu : 2*r + 2*(94-r) + 1 = 189 := by omega
  have hw : 2*(2*r) = 4*r := by omega
  have hrepLow :
      Represents (junc (2*r+2*(94-r)+1) 0 (2*(2*r))) c6 := by
    simpa [hu, hw] using hrep6
  let nLow := 4*(2*r)*(2*r) + 22*(2*r) + 18*(94-r) + 79
  obtain ⟨d,hLow,hrepD,_,_⟩ :=
    low42_raw_head_any_c01_free (2*r) (94-r) c6 hrepLow
  have hwidth : 4*(2*r) + 4*(94-r) + 12 = 4*(r+97) := by omega
  have hrepD' : Represents (junc 0 0 (4*(r+97))) d := by
    simpa [hwidth] using hrepD
  have htotal :
      run target429 (46692+nLow) c = some d :=
    physical_run_add_of_endpoint 46692 nLow c c6 d houter hLow
  have hfreeD := junc0_physical_c01_free 0 (4*(r+97)) d hrepD'
  have hliveD := junc0_physical_live 0 (4*(r+97)) d hrepD'
  have hprefix := physical_run_prefix_c01_free
    (46692+nLow) c d htotal hfreeD hliveD
  exact ⟨d, htotal, hrepD', by simpa [nLow] using hprefix⟩

#print axioms junc0_return_map_28

end BB429Junc0ReturnMap28
