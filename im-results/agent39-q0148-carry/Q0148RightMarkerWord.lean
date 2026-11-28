import Q0148MarkerTrain
import Q0148FirstMarkerReturn
import Lean.Elab.Tactic.Omega

/-!
# Exact boundary-reset right tape = arbitrary finite train of 110 markers

This resolves the source-level word matching between Agent5's
two/three blank-turn carry output and the uniform marked E1 source
train. The internal source chunk M=11010 must be read as a physical
marker B=110 followed by one physical A=10 guard. For ANY finite
list of old even gap exponents, and ANY number of additional M
markers at the far edge, the reversed chunk output has exactly the
rightMarkers grammar with its last A guard explicit. There is NO
finite simulation bound and NO appeal to inferred physical gaps.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- A list of k extra separated markers, built by right append to
    make the reversed outputBits recursion syntactically direct. -/
def markerTail : Nat → List LeftChunk
  | 0 => []
  | k+1 => markerTail k ++ [.separatedMarker]

/-- Exactly A B followed by the smaller right-marker word at each
    added far-edge M, for ANY k. -/
theorem markerTail_word (k : Nat) :
    [true,false] ++ outputBits (markerTail k) =
      rightMarkers (List.replicate k 0) [true,false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [markerTail,outputBits_append,rightMarkers,
        outputBits,chunkBits,rep,ih,List.append_assoc,List.replicate_succ]

/-- One normalized marker block M A^(2u) in the SOURCE chunk list
    becomes A^(2u+1) B at the physical right edge, and leaves the
    same leading A guard for the next source chunk. -/
theorem prepend_even_block (u : Nat) (cs : List LeftChunk) :
    [true,false] ++
      outputBits (cs ++ (.separatedMarker :: aRun (2*u))) =
    rep [true,false] (2*u+1) ++ [true,true,false] ++
      ([true,false] ++ outputBits cs) := by
  rw [outputBits_append]
  simp [outputBits,output_aRun,chunkBits,rep,List.append_assoc]

/-- Uniform right-word theorem: the forward order of original right
    gaps is `us` (each 2*u+1 physical As), while the source stack
    stores the same gaps in REVERSED order as normalized blocks. -/
theorem rightMarkerWord (us : List Nat) (k : Nat) :
    [true,false] ++ outputBits
      (markerTail k ++ normalizedBlocks us.reverse) =
      rightMarkers (us.map (fun u => 2*u) ++
          List.replicate k 0) [true,false] := by
  induction us with
  | nil =>
      simpa [rightMarkers,normalizedBlocks] using markerTail_word k
  | cons u us ih =>
      have hform :
          markerTail k ++ normalizedBlocks (u::us).reverse =
            (markerTail k ++ normalizedBlocks us.reverse) ++
              (.separatedMarker :: aRun (2*u)) := by
        simp [List.reverse_cons,normalizedBlocks_append,
          normalizedBlocks,List.append_assoc]
      rw [hform,prepend_even_block]
      simpa [rightMarkers,ih,rep,List.append_assoc]

/-- Exact bitword identification for the a=1 blank-turn reset:
    one extra far-edge M contributes exactly one short final
    right-side marker of gap one. -/
theorem a1_reset_right_markers (us : List Nat) :
    [false,true,false] ++
      outputBits (.separatedMarker :: normalizedBlocks us.reverse) =
    [false] ++
      rightMarkers (us.map (fun u => 2*u) ++ [0]) [true,false] := by
  have h := rightMarkerWord us 1
  simpa [markerTail, rightMarkers,List.append_assoc] using
    congrArg (fun v : List Bool => [false] ++ v) h

/-- a=3 has three extra far-edge markers and correspondingly three
    short right-side marker gaps, rather than the one in a=1. -/
theorem a3_reset_right_markers (us : List Nat) :
    [false,true,false] ++
      outputBits
        ([.separatedMarker,.separatedMarker,.separatedMarker] ++
          normalizedBlocks us.reverse) =
    [false] ++
      rightMarkers (us.map (fun u => 2*u) ++ [0,0,0])
        [true,false] := by
  have h := rightMarkerWord us 3
  simpa [markerTail,rightMarkers,List.append_assoc] using
    congrArg (fun v : List Bool => [false] ++ v) h

#print axioms markerTail_word
#print axioms prepend_even_block
#print axioms rightMarkerWord
#print axioms a1_reset_right_markers
#print axioms a3_reset_right_markers

end BB6.Agent39Q0148Carry
