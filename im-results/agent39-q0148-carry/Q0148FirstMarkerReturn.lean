import Q0148ThreeCarryCycles

/-!
# First all-length E1 marker return after the blank boundary

This is the first source-level head return in the proposed q0-148 gap
recurrence for both a=1 and a=3. The subsequent marker-hop induction,
which gives the FULL far-right boundary return, remains open.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep
open BB6Coverage
open BB6Coverage.Agent31Pump

set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem outputBits_append (xs ys : List LeftChunk) :
    outputBits (xs ++ ys) = outputBits ys ++ outputBits xs := by
  induction xs with
  | nil => simp [outputBits]
  | cons c xs ih =>
      simp only [List.cons_append, outputBits, ih, List.append_assoc]

theorem normalizedBlocks_append (xs ys : List Nat) :
    normalizedBlocks (xs ++ ys) =
      normalizedBlocks xs ++ normalizedBlocks ys := by
  induction xs with
  | nil => rfl
  | cons n xs ih =>
      simp only [List.cons_append, normalizedBlocks, ih, List.append_assoc]

theorem output_aRun (n : Nat) :
    outputBits (aRun n) = rep [true,false] n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change outputBits (aRun n) ++ [true,false] =
        [true,false] ++ rep [true,false] n
      simpa only [ih] using rep_snoc [true,false] n

/-- For any earlier even gaps and any last even gap of length 2n,
    the qA right tape starts with precisely (10)^(2n+2)110.
    This is the exact precondition of Agent5's ARightToEOne source macro.
    The remaining suffix is explicit and unchanged. -/
theorem a3_marker_portal_word (xs : List Nat) (n : Nat) (R : List Bool) :
    carryRight .eleven ++
        outputBits (a3Third (xs ++ [n])) ++ [false] ++ R =
      [true,false,true,false] ++ rep [true,false] (2*n) ++
        [true,true,false] ++
        ([true,false] ++ outputBits (a3Third xs) ++ [false] ++ R) := by
  simp [a3Third, normalizedBlocks_append, normalizedBlocks,
    outputBits_append, output_aRun, carryRight, chunkBits,
    List.append_assoc]

/-- Original source return from an a=3 arbitrary odd-gap boundary
    to the first (leftmost) E1 marker, after three physical blank turns
    and the exact n-parametric ARightToEOne macro. The source theorem
    does not yet hop across the remaining markers. -/
theorem a3_first_e1_source (xs : List Nat) (n : Nat)
    (L R : List Bool) :
    run0 p
      (((a3FirstTime (xs ++ [n]) + a3SecondTime (xs ++ [n])) +
         a3ThirdTime (xs ++ [n])) + (2*(2*n)+6))
      ⟨4,[true,false] ++ inputBits (a3Input (xs ++ [n])) ++
           [false,false,false,false,false,false,false] ++ L,
         [false,true,false,false,false,false,false,false] ++ R⟩ =
    some ⟨4,
      [true,false,true] ++ rep [false,true] (2*n+1) ++
        [false,true] ++ L,
      [false] ++ [true,false] ++ outputBits (a3Third xs) ++
        [false] ++ R⟩ := by
  have h0 := three_blank_turns_source (xs ++ [n]) L R
  have hb := a3_marker_portal_word xs n R
  rw [hb] at h0
  have h1 := ARightToEOne (2*n) L
    ([true,false] ++ outputBits (a3Third xs) ++ [false] ++ R)
  simpa [Nat.add_assoc, List.append_assoc] using join0 h0 h1

/-- The a=1 branch has only the first two blank turns, no extra U/T
    carry recovery. -/
def a1Input (xs : List Nat) (n : Nat) : List LeftChunk :=
  evenBlocks (xs ++ [n])

def a1First (xs : List Nat) (n : Nat) : List LeftChunk :=
  .separatedMarker :: normalizedBlocks (xs ++ [n])

def a1FirstTime (xs : List Nat) (n : Nat) : Nat :=
  ((4 + 4*scanCost (a1Input xs n)) + 13) +
    (scanCost (a1First xs n) + carryCost .eleven)

theorem a1_marker_portal_word (xs : List Nat) (n : Nat) (R : List Bool) :
    carryRight .eleven ++
        outputBits (a1First xs n) ++ R =
      [true,false,true,false] ++ rep [true,false] (2*n) ++
        [true,true,false] ++
        ([true,false] ++ outputBits (.separatedMarker ::
          normalizedBlocks xs) ++ R) := by
  simp [a1First, normalizedBlocks_append, normalizedBlocks,
    outputBits_append, output_aRun, carryRight, chunkBits,
    List.append_assoc]

/-- Original a=1 source reaches the first E1 marker in a defined,
    strictly positive number of steps for every finite even-gap list.
    The all-marker return still requires the markedHopN induction. -/
theorem a1_first_e1_source (xs : List Nat) (n : Nat)
    (L R : List Bool) :
    run0 p (a1FirstTime xs n + (2*(2*n)+6))
      ⟨4,[true,false] ++ inputBits (a1Input xs n) ++
          [false,false,false] ++ L,
         [false,true,false,false,false] ++ R⟩ =
    some ⟨4,
      [true,false,true] ++ rep [false,true] (2*n+1) ++
        [false,true] ++ L,
      [false] ++ [true,false] ++ outputBits
        (.separatedMarker :: normalizedBlocks xs) ++ R⟩ := by
  have h0 : run0 p (a1FirstTime xs n)
      ⟨4,[true,false] ++ inputBits (a1Input xs n) ++
          [false,false,false] ++ L,
         [false,true,false,false,false] ++ R⟩ =
      some ⟨0,[false] ++ L,
        carryRight .eleven ++ outputBits (a1First xs n) ++ R⟩ := by
    have h := twoBlankTurns (a1Input xs n) L R
    simpa [a1FirstTime, a1Input, a1First,
      block_normalization_output, List.append_assoc] using h
  have hb := a1_marker_portal_word xs n R
  rw [hb] at h0
  have h1 := ARightToEOne (2*n) L
    ([true,false] ++ outputBits
      (.separatedMarker :: normalizedBlocks xs) ++ R)
  simpa [Nat.add_assoc, List.append_assoc] using join0 h0 h1

#print axioms outputBits_append
#print axioms normalizedBlocks_append
#print axioms output_aRun
#print axioms a3_marker_portal_word
#print axioms a3_first_e1_source
#print axioms a1_marker_portal_word
#print axioms a1_first_e1_source

end BB6.Agent39Q0148Carry
