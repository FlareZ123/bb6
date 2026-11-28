import Q0148EvenCarryOutput

/-!
# Exact physical boundary tape encoding for the original Raw11 q0-148

This proves that the SOURCE grammar used by the arbitrary-even-gap
transducer is the literal reversal of the physical W(g) tape, with
the E1 head on the third A of the final A^4. It is independent of
the source machine's transitions and has NO bound on the count or
sizes of interior odd gaps.

Indeed the identity holds for ANY positive first gap (a0+1), not
only the stable source invariant's a∈{1,3}. It removes the possible
off-by-one source grammar assumption at the blank right boundary.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Physical old markers B=110 and intervening odd A-gaps
    (10)^(2u+1), ordered left-to-right. -/
def physSegments : List Nat → List Bool
  | [] => []
  | u::us =>
      [true,true,false] ++ rep [true,false] (2*u+1) ++ physSegments us

/-- A physical complete boundary tape ends with B A^4; the head is
    at the third (zero-based 2) A, whose bit 1 is included here. -/
def physicalBoundaryLeft (a : Nat) (us : List Nat) : List Bool :=
  (rep [true,false] a ++ physSegments us ++
    [true,true,false] ++ rep [true,false] 2 ++ [true]).reverse

/-- Reversing the physical A=10 block yields copies of 01. -/
theorem reverseA_geometry (n : Nat) :
    (rep [true,false] n).reverse = rep [false,true] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ([true,false] ++ rep [true,false] n).reverse =
        [false,true] ++ rep [false,true] n
      rw [List.reverse_append,ih]
      simpa using rep_snoc [false,true] n

/-- The simple phase-shift identity (01)^n 0 = 0 (10)^n. -/
theorem phase_rotation_geometry (n : Nat) :
    rep [false,true] n ++ [false] =
      [false] ++ rep [true,false] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change [false,true] ++ (rep [false,true] n ++ [false]) =
        [false] ++ ([true,false] ++ rep [true,false] n)
      have h := congrArg (fun z : List Bool => [false,true] ++ z) ih
      simpa [List.append_assoc] using h

/-- Reverse a single physical odd gap and marker: the phase
    boundary moves the marker from 011 to a 11010 carry frame. -/
theorem reversed_marker_geometry (n : Nat) :
    rep [false,true] (n+1) ++ [false,true,true] =
      [false,true,false] ++ rep [true,false] n ++ [true,true] := by
  have h := congrArg
    (fun z : List Bool => [false,true] ++ z ++ [true,true])
    (phase_rotation_geometry n)
  simpa [rep,List.append_assoc] using h

def nearSegments : List Nat → List Bool
  | [] => []
  | u::us =>
      (rep [false,true] (2*u+1) ++ [false,true,true]) ++ nearSegments us

theorem nearSegments_append (xs ys : List Nat) :
    nearSegments (xs ++ ys) = nearSegments xs ++ nearSegments ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [nearSegments,ih,List.append_assoc]

/-- Reversing the physical old-gap word literally reverses the
    chronological gap list and changes 10→01, B=110→011. -/
theorem reverse_segments_geometry (us : List Nat) :
    (physSegments us).reverse = nearSegments us.reverse := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      have hrev :
          (physSegments (u::us)).reverse =
          (physSegments us).reverse ++
            (rep [true,false] (2*u+1)).reverse ++
            [false,true,true] := by
        simp [physSegments,List.reverse_append,List.append_assoc]
      calc
        (physSegments (u::us)).reverse =
          (physSegments us).reverse ++
            (rep [true,false] (2*u+1)).reverse ++
            [false,true,true] := hrev
        _ = nearSegments us.reverse ++
            (rep [false,true] (2*u+1) ++ [false,true,true]) := by
              rw [ih,reverseA_geometry]
              simp only [List.append_assoc]
        _ = nearSegments (us.reverse ++ [u]) := by
              rw [nearSegments_append]
              simp [nearSegments]
        _ = nearSegments (u::us).reverse := by
              simp

/-- Every reversed odd gap adds exactly one source M=11010, with
    only the initial 010 and terminal alternating pair remaining.
    Induction is over an ARBITRARY number of physical markers. -/
theorem input_aRun_geometry (n : Nat) :
    inputBits (aRun n) = rep [true,false] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [aRun,inputBits,chunkBits,rep,ih,List.append_assoc]

theorem telescope_geometry (us : List Nat) (tail : List Bool) :
    nearSegments us ++ ([false,true,false] ++ tail) =
      [false,true,false] ++ inputBits (evenBlocks us) ++ tail := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      have ht := congrArg
        (fun z : List Bool =>
          (rep [false,true] (2*u+1) ++ [false,true,true]) ++ z) ih
      calc
        nearSegments (u::us) ++ ([false,true,false] ++ tail) =
          (rep [false,true] (2*u+1) ++ [false,true,true]) ++
             ([false,true,false] ++ inputBits (evenBlocks us) ++ tail) := by
               simpa [nearSegments,List.append_assoc] using ht
        _ = [false,true,false] ++ inputBits (evenBlocks (u::us)) ++ tail := by
          rw [reversed_marker_geometry (2*u)]
          simp [evenBlocks,inputBits_append,inputBits,
            input_aRun_geometry,chunkBits,List.append_assoc]

/-- The far-left physical A^(a0+1), when reversed, contributes
    exactly the dangling 010 and the source A^a0 tail. -/
theorem tail_geometry (a0 : Nat) :
    rep [false,true] (a0+1) ++ [false] =
      [false,true,false] ++ inputBits (aRun a0) := by
  have h := phase_rotation_geometry (a0+1)
  simpa [input_aRun_geometry,rep,List.append_assoc] using h

/-- THE MAIN ALL-LENGTH PHYSICAL-TO-SOURCE IDENTITY.

    `physicalBoundaryLeft` is the literal reverse physical tape
    prefix from the E1 head towards the left. One exterior zero
    closes its final A pair. For ANY a0 and ANY list us of old
    interior odd gap exponents, it equals the source input word
    for the actual original machine's 2-blank-round gadget. -/
theorem physical_to_source_geometry (a0 : Nat) (us : List Nat) :
    physicalBoundaryLeft (a0+1) us ++ [false] =
      [true,false] ++
        inputBits (evenBlocks (1::us.reverse) ++ aRun a0) := by
  have hrev :
      physicalBoundaryLeft (a0+1) us ++ [false] =
        ([true] ++ rep [false,true] 2 ++ [false,true,true]) ++
           nearSegments us.reverse ++
           (rep [false,true] (a0+1) ++ [false]) := by
    simp [physicalBoundaryLeft,List.reverse_append,
      reverse_segments_geometry,reverseA_geometry,
      List.append_assoc]
  calc
    physicalBoundaryLeft (a0+1) us ++ [false] =
      ([true] ++ rep [false,true] 2 ++ [false,true,true]) ++
        nearSegments us.reverse ++
        (rep [false,true] (a0+1) ++ [false]) := hrev
    _ = ([true] ++ rep [false,true] 2 ++ [false,true,true]) ++
        (nearSegments us.reverse ++
          ([false,true,false] ++ inputBits (aRun a0))) := by
          rw [tail_geometry]
          simp only [List.append_assoc]
    _ = ([true] ++ rep [false,true] 2 ++ [false,true,true]) ++
        ([false,true,false] ++ inputBits (evenBlocks us.reverse) ++
          inputBits (aRun a0)) := by
            rw [telescope_geometry]
    _ = [true,false] ++
        inputBits (evenBlocks (1::us.reverse) ++ aRun a0) := by
          simp [evenBlocks,inputBits_append,inputBits,
            aRun,chunkBits,rep,List.append_assoc]

#print axioms reverseA_geometry
#print axioms phase_rotation_geometry
#print axioms reversed_marker_geometry
#print axioms reverse_segments_geometry
#print axioms telescope_geometry
#print axioms tail_geometry
#print axioms physical_to_source_geometry

end BB6.Agent39Q0148Carry
