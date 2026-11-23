import Lean.Elab.Tactic.Omega
import YPlusZClosure

/-!
  A fully original-source trace for a *synthetic* exceptional P2/Y3 seed
  missed by the existing Y/Z sufficient regularization grammar. This is
  not claimed to be blank-reachable, halting, or nonhalting.

  Path:
  fixed P2 reset; 4 guarded B/E edges; E/p0 Y3->Y2;
  5 guarded B/E edges; E/p2 Y2->Z3; 4 guarded B/E edges.
  Precisely isolates the next missing source exit as E/p2,Z3,q=8.
-/

namespace BB6.Agent36Residual146779

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerTower (marker)
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 18000000
set_option maxRecDepth 8192

private theorem n0 :
    (normalizeWithCount (⟨1174237,0,6⟩ : Packet)).2 =
      (⟨59378713,2,0⟩ : Packet) := by
      simp [normalizeWithCount,advance]

private theorem n1 :
    (normalizeWithCount (⟨158343229,0,11⟩ : Packet)).2 =
      (⟨21352225930,4,2⟩ : Packet) := by
      simp [normalizeWithCount,advance]

private theorem n2 :
    (normalizeWithCount (⟨56939269141,0,14⟩ : Packet)).2 =
      (⟨2879299338241,8,2⟩ : Packet) := by
      simp [normalizeWithCount,advance]

/-- Exact original-machine source transport through all 13 guarded
    B/E edges and both exceptional marker transforms. -/
theorem residual_source :
    ∃ T : Nat,
      run T
        (packet 440341 0 2 (false :: List.replicate 6 true)) =
      packet 2879299338241 8 2
        (BB6.Agent2MarkerZero.marker 3) := by
  let y3 := marker 3
  let y2 := marker 2
  let z3 := BB6.Agent2MarkerZero.marker 3
  obtain ⟨t0,h0⟩ :=
    normalized_original_source
      (⟨1174237,0,6⟩ : Packet) (by decide) y3
  obtain ⟨t1,h1⟩ :=
    normalized_original_source
      (⟨158343229,0,11⟩ : Packet) (by decide) y2
  obtain ⟨t2,h2⟩ :=
    normalized_original_source
      (⟨56939269141,0,14⟩ : Packet) (by decide) z3
  have hs0 :
      run t0 (packet 1174237 0 6 y3) =
        packet 59378713 2 0 y3 := by
    simpa [toState,BB6.Agent31PacketPaths.physical,n0] using h0
  have hs1 :
      run t1 (packet 158343229 0 11 y2) =
        packet 21352225930 4 2 y2 := by
    simpa [toState,BB6.Agent31PacketPaths.physical,n1] using h1
  have hs2 :
      run t2 (packet 56939269141 0 14 z3) =
        packet 2879299338241 8 2 z3 := by
    simpa [toState,BB6.Agent31PacketPaths.physical,n2] using h2
  have hr :
      run (BB6.Agent2PacketP2Reset.eTwoTime 146779 0)
        (packet 440341 0 2 (false :: List.replicate 6 true)) =
      packet 1174237 0 6 y3 := by
    simpa [y3,marker,BB6.Agent2PacketP2Reset.marker] using
      (BB6.Agent2PacketP2Reset.e_two_reset 146779 0)
  let tz : Nat := 12*19792903*19792903+49*19792903+50+4*2
  have hz :
      run tz (packet 59378713 2 0 y3) =
      packet 158343229 0 11 y2 := by
    simpa [tz,y3,y2] using
      (BB6.Agent2MarkerTower.e_zero_drop 19792903 2 2)
  let te : Nat := 12*7117408642*7117408642+49*7117408642+68+4*4+6*1
  have he :
      run te (packet 21352225930 4 2 y2) =
      packet 56939269141 0 14 z3 := by
    simpa [te,y2,z3] using
      (BB6.Agent2EAltPacketCompose.e_two_to_zero 7117408642 4 1)
  refine ⟨BB6.Agent2PacketP2Reset.eTwoTime 146779 0 +
    (t0+(tz+(t1+(te+t2)))),?_⟩
  rw [run_add,hr,run_add,hs0,run_add,hz,run_add,hs1,
      run_add,he,hs2]

#print axioms residual_source
end BB6.Agent36Residual146779
