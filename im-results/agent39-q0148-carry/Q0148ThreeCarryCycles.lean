import Q0148EvenCarryOutput
import Lean.Elab.Tactic.Omega

/-!
# All-length, original-machine three-cycle blank-boundary macro

The a=3 boundary case is the hard one: after the first two blank
turns its carry is U; two more complete blank cycles normalize it
through T back to S. All words below have arbitrarily many even-length
A-gaps. This does NOT yet prove the next E1 return or the full
blank-derived nonhalting theorem.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- The generated output has moved each marker in front of the
    preceding even A-run; appending one marker recovers the input
    language prefixed by that marker. -/
theorem normalized_marker (ns : List Nat) :
    normalizedBlocks ns ++ [.separatedMarker] =
      .separatedMarker :: evenBlocks ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp [normalizedBlocks, evenBlocks, ih, List.append_assoc]

def a3Input (ns : List Nat) : List LeftChunk := evenBlocks ns ++ aRun 2

def a3First (ns : List Nat) : List LeftChunk :=
  .separatedMarker :: (normalizedBlocks ns ++ [.separatedMarker])

def a3Second (ns : List Nat) : List LeftChunk :=
  [.separatedMarker,.separatedMarker] ++ normalizedBlocks ns

def a3Third (ns : List Nat) : List LeftChunk :=
  [.separatedMarker,.separatedMarker,.separatedMarker] ++ normalizedBlocks ns

/-- Exactly one further boundary cycle turns the U residue into T,
    and emits precisely TWO leading markers. -/
theorem second_cycle_output (ns : List Nat) :
    carryFold .eleven (a3First ns ++ [.alternating]) =
      (a3Second ns, .elevenZeroOne) := by
  have hw :
      a3First ns ++ [.alternating] =
        ([.separatedMarker,.separatedMarker] ++ evenBlocks ns) ++
          [.alternating] := by
    simp [a3First, normalized_marker, List.append_assoc]
  rw [hw, fold_append]
  have hp : carryFold .eleven
      ([.separatedMarker,.separatedMarker] ++ evenBlocks ns) =
      ([.separatedMarker,.separatedMarker] ++ normalizedBlocks ns, .eleven) := by
    simp [fold_append, block_normalization_output, carryFold, carryStep]
  rw [hp]
  dsimp only
  simp [a3Second,carryFold,carryStep,List.append_assoc]

/-- A second further boundary cycle turns T into S, and emits exactly
    THREE leading markers. The rest is the unchanged normal form. -/
theorem third_cycle_output (ns : List Nat) :
    carryFold .eleven (a3Second ns ++ [.separatedMarker]) =
      (a3Third ns, .eleven) := by
  have hw :
      a3Second ns ++ [.separatedMarker] =
        [.separatedMarker,.separatedMarker,.separatedMarker] ++ evenBlocks ns := by
    simp [a3Second, normalized_marker, List.append_assoc]
  rw [hw, fold_append]
  have hp : carryFold .eleven
      [.separatedMarker,.separatedMarker,.separatedMarker] =
      ([.separatedMarker,.separatedMarker,.separatedMarker], .eleven) := by
    rfl
  rw [hp]
  dsimp only
  rw [block_normalization_output]
  simp [a3Third,List.append_assoc]

def a3FirstTime (ns : List Nat) : Nat :=
  ((4 + 4*scanCost (a3Input ns)) + 13) +
    (scanCost (a3First ns) + carryCost .one)

def a3SecondTime (ns : List Nat) : Nat :=
  (rightScanCost (toRight .alternating :: rightSequence (a3First ns)) + 2) +
    (scanCost (a3Second ns) + carryCost .elevenZeroOne)

def a3ThirdTime (ns : List Nat) : Nat :=
  (rightScanCost (toRight .separatedMarker :: rightSequence (a3Second ns)) + 2) +
    (scanCost (a3Third ns) + carryCost .eleven)

/-- Three original-source blank-boundary sweeps, for an UNBOUNDED
    number of odd tape gaps. Each source step is defined by the open
    F1 table p. The output has returned to the S carry and has gained
    exactly two markers at the far boundary. This is a strict positive
    run, not an assumed symbolic transition. Extra zero padding lets
    us compose the three physically exact run0 gadgets. -/
theorem three_blank_turns_source (ns : List Nat) (L R : List Bool) :
    run0 p ((a3FirstTime ns + a3SecondTime ns) + a3ThirdTime ns)
      ⟨4,
        [true,false] ++ inputBits (a3Input ns) ++
          [false,false,false,false,false,false,false] ++ L,
        [false,true,false,false,false,false,false,false] ++ R⟩ =
    some ⟨0,[false] ++ L,
      carryRight .eleven ++ outputBits (a3Third ns) ++ [false] ++ R⟩ := by
  have h0 : run0 p (a3FirstTime ns)
      ⟨4,[true,false] ++ inputBits (a3Input ns) ++
          [false,false,false,false,false,false,false] ++ L,
         [false,true,false,false,false,false,false,false] ++ R⟩ =
      some ⟨0,[false,false,false,false,false] ++ L,
        carryRight .one ++ outputBits (a3First ns) ++
          [false,false,false] ++ R⟩ := by
    have h := twoBlankTurns (a3Input ns)
      ([false,false,false,false] ++ L) ([false,false,false] ++ R)
    simpa [a3FirstTime, a3First, a3Input, terminal_two_output,
      List.append_assoc, carryRight] using h
  have h1 : run0 p (a3SecondTime ns)
      ⟨0,[false,false,false,false,false] ++ L,
        carryRight .one ++ outputBits (a3First ns) ++
          [false,false,false] ++ R⟩ =
      some ⟨0,[false,false,false] ++ L,
        carryRight .elevenZeroOne ++ outputBits (a3Second ns) ++
          [false,false] ++ R⟩ := by
    have h := anotherBlankCycle .alternating (a3First ns)
      ([false,false] ++ L) ([false] ++ R)
    simpa [a3SecondTime, second_cycle_output, carryRight, chunkBits,
      List.append_assoc] using h
  have h2 : run0 p (a3ThirdTime ns)
      ⟨0,[false,false,false] ++ L,
        carryRight .elevenZeroOne ++ outputBits (a3Second ns) ++
          [false,false] ++ R⟩ =
      some ⟨0,[false] ++ L,
        carryRight .eleven ++ outputBits (a3Third ns) ++ [false] ++ R⟩ := by
    have h := anotherBlankCycle .separatedMarker (a3Second ns) L R
    simpa [a3ThirdTime, third_cycle_output, carryRight, chunkBits,
      List.append_assoc] using h
  have h := join0 h0 (join0 h1 h2)
  simpa [Nat.add_assoc] using h

#print axioms normalized_marker
#print axioms second_cycle_output
#print axioms third_cycle_output
#print axioms three_blank_turns_source

end BB6.Agent39Q0148Carry
