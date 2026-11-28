import Q0148GenericGapChain
import Q0148BoundaryGeometry
import Lean.Elab.Tactic.Omega

/-!
# The final ALL-LENGTH source marker train returns to the exact
# original physical stable boundary grammar, not merely to an E1
# state with an unspecified left tape.

For any arbitrary list of crossed EVEN marker parameters (2*u), the
high endpoint's left chunk stack is literally E([1,u+1,...])A^2,
and the low endpoint is literally E([1,u+1,...])A^0. Combined with
the accepted arbitrary-even-gap normalization theorem and the
physical-to-source geometry theorem this identifies the far-right
E1 return and the new old-gap vector of the source P recurrence.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem gapChain_append (xs ys : List Nat) :
    gapChain (xs ++ ys) = gapChain xs ++ gapChain ys := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
      simp [gapChain, ih, List.append_assoc]

/-- Telescoping output at the LOW far endpoint: every marker chain
    whose source gap parameters are even contains exactly the
    EVEN-BLOCK physical boundary grammar, with no far-left As. -/
theorem gapChain_low_closed (us : List Nat) :
    gapChain (us.map (fun u => 2*u)) ++ [.separatedMarker] =
      .separatedMarker ::
        evenBlocks (us.map (fun u => u+1)) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      have hu : 2*u+2 = 2*(u+1) := by omega
      have h := congrArg
        (fun xs : List LeftChunk =>
          (.separatedMarker :: aRun (2*u+2)) ++ xs) ih
      simpa [gapChain,evenBlocks,hu,List.append_assoc] using h

/-- The HIGH far endpoint differs from LOW by exactly two
    alternating tokens AFTER the terminal marker. -/
theorem gapChain_high_closed (us : List Nat) :
    gapChain (us.map (fun u => 2*u) ++ [0]) =
      .separatedMarker ::
        (evenBlocks (us.map (fun u => u+1)) ++ aRun 2) := by
  rw [gapChain_append]
  have h := congrArg
    (fun z : List LeftChunk => z ++ aRun 2)
    (gapChain_low_closed us)
  simpa [gapChain,List.append_assoc,aRun] using h

/-- Final HIGH source left stack in EXACT E/A grammar: new a=3,
    every crossed old even marker parameter 2u gives new old gap
    2(u+1)+1, and the rightmost A^4 head frame is retained. -/
theorem high_boundary_chunks (us : List Nat) :
    aRun 2 ++ gapChain (us.map (fun u => 2*u) ++ [0]) =
      evenBlocks (1 :: us.map (fun u => u+1)) ++ aRun 2 := by
  rw [gapChain_high_closed]
  simp [evenBlocks,List.append_assoc]

/-- Final LOW source left stack is the same returned odd-gap
    interior but starts with far-left a=1. -/
theorem low_boundary_chunks (us : List Nat) :
    (aRun 2 ++ gapChain (us.map (fun u => 2*u))) ++
      [.separatedMarker] =
      evenBlocks (1 :: us.map (fun u => u+1)) := by
  have h := gapChain_low_closed us
  simpa [evenBlocks,List.append_assoc] using
    congrArg (fun z : List LeftChunk => aRun 2 ++ z) h

/-- The source bitwords at the HIGH boundary are literally the
    physical W(3; new odd gaps) tape, including the exterior zero
    that closes the final far-left A. -/
theorem high_source_to_physical (us : List Nat) :
    [true,false] ++
      inputBits (aRun 2 ++
        gapChain (us.map (fun u => 2*u) ++ [0])) =
    physicalBoundaryLeft 3 (us.map (fun u => u+1)).reverse ++ [false] := by
  rw [high_boundary_chunks]
  have h := physical_to_source_geometry 2
    (us.map (fun u => u+1)).reverse
  simpa [List.reverse_reverse,List.append_assoc] using h.symm

/-- Analogous exact physical boundary word for the low a=1
    endpoint; the last marker closes without further As. -/
theorem low_source_to_physical (us : List Nat) :
    [true,false] ++
      inputBits ((aRun 2 ++
        gapChain (us.map (fun u => 2*u))) ++ [.separatedMarker]) =
    physicalBoundaryLeft 1 (us.map (fun u => u+1)).reverse ++ [false] := by
  rw [low_boundary_chunks]
  have h := physical_to_source_geometry 0
    (us.map (fun u => u+1)).reverse
  simpa [List.reverse_reverse,List.append_assoc] using h.symm

#print axioms gapChain_append
#print axioms gapChain_low_closed
#print axioms gapChain_high_closed
#print axioms high_boundary_chunks
#print axioms low_boundary_chunks
#print axioms high_source_to_physical
#print axioms low_source_to_physical

end BB6.Agent39Q0148Carry
