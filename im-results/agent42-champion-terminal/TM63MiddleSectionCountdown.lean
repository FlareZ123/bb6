import TM63MiddleSectionPrefix4
import M1OddResidueThree
import M0EvenResidueTwo
import M1ZeroOddQ4Prefix
import TM63RootCountdownArithmetic
import TM63M1OddRst1PrimeContinuation
import Lean.Elab.Tactic.Omega

/-!
# Root-specific TM63 middle-section countdown

Compose the already-proved first four residue rows with the actual next
three rows (3,1), (2,0), and (1,2).  The genuine TM63 root has
tm63Index1 = 8*k+7 with odd k, so these seven original-table increments
reach exactly S1(L,8*k,1,...).  Then the root-specific (0,1) row at n=8*k
reaches the next (7,0) row, which is the input family being handled by
Agent 41.

This file is an integration theorem, not a claim that the upstream
counted-drain dependency graph is axiom-clean or that the full TM63
itinerary halts.  The source workflow must check its transitive axioms.
-/

namespace BB6Coverage.Agent42MiddleSectionCountdown

open BB6Coverage
open BB6ChampionArithmetic
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42MiddleSectionPrefix4
open BB6Coverage.Agent42M2OddGeneric
open BB6Coverage.Agent8M1OddResidueThree
open BB6Coverage.Agent24M0EvenResidueTwo
open BB6Coverage.Agent48M1ZeroOddQ4Prefix
open BB6Coverage.Agent8Rst1PrimeRoot

private theorem nextExponent_pos (m a b : Nat) (ha : 0 < a) :
    0 < nextExponent m a b := by
  unfold nextExponent
  omega

def middleAfter5A (a b : Nat) : Nat :=
  nextExponent 1 (middleAfter4A a b) (middleAfter4B b)

def middleAfter5B (b : Nat) : Nat :=
  nextRight (middleAfter4B b)

def middleAfter6A (a b : Nat) : Nat :=
  nextExponent 0 (middleAfter5A a b) (middleAfter5B b)

def middleAfter6B (b : Nat) : Nat :=
  nextRight (middleAfter5B b)

def middleAfter7A (a b : Nat) : Nat :=
  nextExponent 2 (middleAfter6A a b) (middleAfter6B b)

def middleAfter7B (b : Nat) : Nat :=
  nextRight (middleAfter6B b)

def middleAfter8A (a b : Nat) : Nat :=
  nextExponent 1 (middleAfter7A a b) (middleAfter7B b)

def middleAfter8B (b : Nat) : Nat :=
  nextRight (middleAfter7B b)

/-- Exact cost of the first seven middle-section decrements. -/
def middleFirst7Cost (k a b : Nat) : Nat :=
  middleFirst4Cost k a b +
  proposedIncrementCost 1 (8*k+3) (middleAfter4A a b) (middleAfter4B b) +
  proposedIncrementCost 0 (8*k+2) (middleAfter5A a b) (middleAfter5B b) +
  proposedIncrementCost 2 (8*k+1) (middleAfter6A a b) (middleAfter6B b)

/-- Exact cost through the root-specific (0,1) row at n=8*k. -/
def middleFirst8Cost (k a b : Nat) : Nat :=
  middleFirst7Cost k a b +
  proposedIncrementCost 1 (8*k) (middleAfter7A a b) (middleAfter7B b)

/-- Total head displacement through the first seven middle-section rows. -/
def middleFirst7HeadShift (b : Nat) : Nat :=
  middleFirst4HeadShift b +
  (5+3*middleAfter4B b) +
  (5+3*middleAfter5B b) +
  (5+3*middleAfter6B b)

/-- Total head displacement through the eighth, root-specific row. -/
def middleFirst8HeadShift (b : Nat) : Nat :=
  middleFirst7HeadShift b + (5+3*middleAfter7B b)

private theorem run_compose
    {c d e : Config} {t u : Nat}
    (h1 : run tm2 t c = some d)
    (h2 : run tm2 u d = some e) :
    run tm2 (t+u) c = some e := by
  rw [run_add, h1]
  simpa using h2

/-- The actual seven-row source composition for the path
(7,2),(6,1),(5,0),(4,2),(3,1),(2,0),(1,2).
The endpoint has marker 1 and index 8*k. -/
theorem tm63_middle_first7_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hbound : 8*k+7 < 2^L) (ha : 0 < a) :
    run tm2 (middleFirst7Cost k a b)
      (s1Config L (8*k+7) 2 a 0 b h) =
      some (s1Config L (8*k) 1
        (middleAfter7A a b) 0 (middleAfter7B b)
        (h + (middleFirst7HeadShift b : Int))) := by
  let a4 := middleAfter4A a b
  let b4 := middleAfter4B b
  let a5 := middleAfter5A a b
  let b5 := middleAfter5B b
  let a6 := middleAfter6A a b
  let b6 := middleAfter6B b
  let a7 := middleAfter7A a b
  let b7 := middleAfter7B b
  let head4 : Int := h + (middleFirst4HeadShift b : Int)
  let head5 : Int := head4+5+3*b4
  let head6 : Int := head5+5+3*b5
  let head7 : Int := head6+5+3*b6

  have hfirst4 :
      run tm2 (middleFirst4Cost k a b)
        (s1Config L (8*k+7) 2 a 0 b h) =
        some (s1Config L (8*k+3) 1 a4 0 b4 head4) := by
    simpa [a4,b4,head4] using
      tm63_middle_first4_source L k a b h (by omega) hbound ha

  have ha1 : 0 < middleAfter1A a b :=
    nextExponent_pos 2 a b ha
  have ha2 : 0 < middleAfter2A a b :=
    nextExponent_pos 1 (middleAfter1A a b) (middleAfter1B b) ha1
  have ha3 : 0 < middleAfter3A a b :=
    nextExponent_pos 0 (middleAfter2A a b) (middleAfter2B b) ha2
  have ha4 : 0 < a4 := by
    dsimp [a4,middleAfter4A]
    exact nextExponent_pos 2 (middleAfter3A a b) (middleAfter3B b) ha3
  have ha5 : 0 < a5 := by
    dsimp [a5,middleAfter5A]
    exact nextExponent_pos 1 a4 b4 ha4
  have ha6 : 0 < a6 := by
    dsimp [a6,middleAfter6A]
    exact nextExponent_pos 0 a5 b5 ha5

  have h5run :
      run tm2 (proposedIncrementCost 1 (8*k+3) a4 b4)
        (s1Config L (8*k+3) 1 a4 0 b4 head4) =
        some (s1Config L (8*k+2) 0 a5 0 b5 head5) := by
    have hraw := m1OddResidueThree_counted_increment_source
      L k a4 b4 head4 (by omega) (by omega) ha4
    simpa [a5,b5,head5,middleAfter5A,middleAfter5B,
      nextExponent,nextRight] using hraw

  have h6run :
      run tm2 (proposedIncrementCost 0 (8*k+2) a5 b5)
        (s1Config L (8*k+2) 0 a5 0 b5 head5) =
        some (s1Config L (8*k+1) 2 a6 0 b6 head6) := by
    have hraw := m0Even_residue2_counted_increment_source
      L k a5 b5 head5 (by omega) (by omega) ha5
    simpa [a6,b6,head6,middleAfter6A,middleAfter6B,
      nextExponent,nextRight] using hraw

  have h7run :
      run tm2 (proposedIncrementCost 2 (8*k+1) a6 b6)
        (s1Config L (8*k+1) 2 a6 0 b6 head6) =
        some (s1Config L (8*k) 1 a7 0 b7 head7) := by
    have hraw := m2Odd_counted_increment_source
      L (8*k+1) a6 b6 head6 (by omega) (by omega)
    have hn : (8*k+1)-1 = 8*k := by omega
    simpa [hn,a7,b7,head7,middleAfter7A,middleAfter7B,
      nextExponent,nextRight] using hraw

  have h01 := run_compose hfirst4 h5run
  have h012 := run_compose h01 h6run
  have h0123 := run_compose h012 h7run
  have hhead : h + (middleFirst7HeadShift b : Int) = head7 := by
    dsimp [middleFirst7HeadShift,middleFirst4HeadShift,
      head7,head6,head5,head4,
      middleAfter1B,middleAfter2B,middleAfter3B,
      middleAfter4B,middleAfter5B,middleAfter6B,nextRight]
    omega
  rw [hhead]
  simpa [middleFirst7Cost,a4,b4,a5,b5,a6,b6,a7,b7,
    middleAfter5A,middleAfter5B,middleAfter6A,middleAfter6B,
    middleAfter7A,middleAfter7B,nextExponent,nextRight] using h0123

/-- Append the genuine-root (m,n)=(1,8*k) source row.  Oddness of k is
essential: it is the exact path parameter produced by tm63Index1. -/
theorem tm63_middle_first8_source
    (L k a b : Nat) (h : Int)
    (hL : 4 ≤ L) (hkodd : k % 2 = 1)
    (hbound : 8*k+7 < 2^L) (ha : 0 < a) :
    run tm2 (middleFirst8Cost k a b)
      (s1Config L (8*k+7) 2 a 0 b h) =
      some (s1Config L (8*k-1) 0
        (middleAfter8A a b) 0 (middleAfter8B b)
        (h + (middleFirst8HeadShift b : Int))) := by
  let a7 := middleAfter7A a b
  let b7 := middleAfter7B b
  let a8 := middleAfter8A a b
  let b8 := middleAfter8B b
  let head7 : Int := h + (middleFirst7HeadShift b : Int)
  let head8 : Int := head7+5+3*b7
  have hfirst7 :
      run tm2 (middleFirst7Cost k a b)
        (s1Config L (8*k+7) 2 a 0 b h) =
        some (s1Config L (8*k) 1 a7 0 b7 head7) := by
    simpa [a7,b7,head7] using
      tm63_middle_first7_source L k a b h hL hbound ha
  have ha1 : 0 < middleAfter1A a b :=
    nextExponent_pos 2 a b ha
  have ha2 : 0 < middleAfter2A a b :=
    nextExponent_pos 1 (middleAfter1A a b) (middleAfter1B b) ha1
  have ha3 : 0 < middleAfter3A a b :=
    nextExponent_pos 0 (middleAfter2A a b) (middleAfter2B b) ha2
  have ha4 : 0 < middleAfter4A a b :=
    nextExponent_pos 2 (middleAfter3A a b) (middleAfter3B b) ha3
  have ha5 : 0 < middleAfter5A a b :=
    nextExponent_pos 1 (middleAfter4A a b) (middleAfter4B b) ha4
  have ha6 : 0 < middleAfter6A a b :=
    nextExponent_pos 0 (middleAfter5A a b) (middleAfter5B b) ha5
  have ha7 : 0 < a7 := by
    dsimp [a7,middleAfter7A]
    exact nextExponent_pos 2 (middleAfter6A a b) (middleAfter6B b) ha6
  have h8run :
      run tm2 (proposedIncrementCost 1 (8*k) a7 b7)
        (s1Config L (8*k) 1 a7 0 b7 head7) =
        some (s1Config L (8*k-1) 0 a8 0 b8 head8) := by
    have hraw := m1ZeroOdd_residue0_counted_increment_source
      L k a7 b7 head7 hL hkodd (by omega) ha7
    simpa [a8,b8,head8,middleAfter8A,middleAfter8B,
      nextExponent,nextRight] using hraw
  have hcomp := run_compose hfirst7 h8run
  have hhead : h + (middleFirst8HeadShift b : Int) = head8 := by
    dsimp [middleFirst8HeadShift,middleFirst7HeadShift,
      middleFirst4HeadShift,head8,head7,
      middleAfter1B,middleAfter2B,middleAfter3B,
      middleAfter4B,middleAfter5B,middleAfter6B,middleAfter7B,nextRight]
    omega
  rw [hhead]
  simpa [middleFirst8Cost,middleFirst7Cost,a7,b7,a8,b8,
    middleAfter5A,middleAfter5B,middleAfter6A,middleAfter6B,
    middleAfter7A,middleAfter7B,middleAfter8A,middleAfter8B,
    nextExponent,nextRight] using hcomp

/-- The actual first-reset length is large enough for every source row
used by the root-specific seven/eight-step composition. -/
private theorem tm63_middle_length_ge_four : 4 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  dsimp [tm63Length1]
  omega

private theorem tm63_middle_root_bound :
    8*tm63RootMiddleK+7 < 2^tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  have hL : tm63Length1 = tm63FirstSection.exponent+5 := by
    dsimp [tm63Length1]
    omega
  have hp : 2^tm63Length1 =
      32*2^tm63FirstSection.exponent := by
    rw [hL,Nat.pow_add]
    norm_num
  rw [← tm63_index1_eq_8k7,tm63_index1_exact,hp]
  omega

private theorem tm63_middle_root_a_pos :
    0 < tm63FirstSection.right := by
  exact sectionResult_right_pos 7 2 6 63 (by decide)

private theorem tm63_middle_after7_a_pos :
    0 < middleAfter7A tm63FirstSection.right
      (nextRight tm63FirstSection.right) := by
  have ha1 := nextExponent_pos 2 tm63FirstSection.right
    (nextRight tm63FirstSection.right) tm63_middle_root_a_pos
  have ha2 := nextExponent_pos 1
    (middleAfter1A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter1B (nextRight tm63FirstSection.right)) ha1
  have ha3 := nextExponent_pos 0
    (middleAfter2A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter2B (nextRight tm63FirstSection.right)) ha2
  have ha4 := nextExponent_pos 2
    (middleAfter3A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter3B (nextRight tm63FirstSection.right)) ha3
  have ha5 := nextExponent_pos 1
    (middleAfter4A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter4B (nextRight tm63FirstSection.right)) ha4
  have ha6 := nextExponent_pos 0
    (middleAfter5A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter5B (nextRight tm63FirstSection.right)) ha5
  have ha7 := nextExponent_pos 2
    (middleAfter6A tm63FirstSection.right (nextRight tm63FirstSection.right))
    (middleAfter6B (nextRight tm63FirstSection.right)) ha6
  simpa [middleAfter7A] using ha7

def tm63MiddleFirst7Moves : Nat :=
  middleFirst7Cost tm63RootMiddleK tm63FirstSection.right
    (nextRight tm63FirstSection.right)

def tm63MiddleFirst8Moves : Nat :=
  middleFirst8Cost tm63RootMiddleK tm63FirstSection.right
    (nextRight tm63FirstSection.right)

def tm63MiddleAfter7A : Nat :=
  middleAfter7A tm63FirstSection.right
    (nextRight tm63FirstSection.right)

def tm63MiddleAfter7B : Nat :=
  middleAfter7B (nextRight tm63FirstSection.right)

def tm63MiddleAfter7Head : Int :=
  tm63AfterFirstResetHead +
    (middleFirst7HeadShift (nextRight tm63FirstSection.right) : Int)

def tm63MiddleAfter8A : Nat :=
  middleAfter8A tm63FirstSection.right
    (nextRight tm63FirstSection.right)

def tm63MiddleAfter8B : Nat :=
  middleAfter8B (nextRight tm63FirstSection.right)

def tm63MiddleAfter8Head : Int :=
  tm63AfterFirstResetHead +
    (middleFirst8HeadShift (nextRight tm63FirstSection.right) : Int)

/-- The seven middle-section source rows start at the authentic endpoint
of the first Rst1' reset, not at a guessed S1 configuration. -/
theorem tm63_middle_first7_root_source :
    run tm2 tm63MiddleFirst7Moves
      (s1Config tm63Length1 tm63Index1 2
        tm63FirstSection.right 0 (nextRight tm63FirstSection.right)
        tm63AfterFirstResetHead) =
      some (s1Config tm63Length1 (8*tm63RootMiddleK) 1
        tm63MiddleAfter7A 0 tm63MiddleAfter7B tm63MiddleAfter7Head) := by
  rw [tm63_index1_eq_8k7]
  simpa [tm63MiddleFirst7Moves,tm63MiddleAfter7A,
    tm63MiddleAfter7B,tm63MiddleAfter7Head] using
    tm63_middle_first7_source tm63Length1 tm63RootMiddleK
      tm63FirstSection.right (nextRight tm63FirstSection.right)
      tm63AfterFirstResetHead
      tm63_middle_length_ge_four tm63_middle_root_bound
      tm63_middle_root_a_pos

/-- Append Agent 48's odd-k (0,1) source row.  Its endpoint is exactly
n=8*k-1, marker 0, the (7,0) family used by the next root-stage owner. -/
theorem tm63_middle_first8_root_source :
    run tm2 tm63MiddleFirst8Moves
      (s1Config tm63Length1 tm63Index1 2
        tm63FirstSection.right 0 (nextRight tm63FirstSection.right)
        tm63AfterFirstResetHead) =
      some (s1Config tm63Length1 (8*tm63RootMiddleK-1) 0
        tm63MiddleAfter8A 0 tm63MiddleAfter8B tm63MiddleAfter8Head) := by
  rw [tm63_index1_eq_8k7]
  simpa [tm63MiddleFirst8Moves,tm63MiddleAfter8A,
    tm63MiddleAfter8B,tm63MiddleAfter8Head] using
    tm63_middle_first8_source tm63Length1 tm63RootMiddleK
      tm63FirstSection.right (nextRight tm63FirstSection.right)
      tm63AfterFirstResetHead
      tm63_middle_length_ge_four tm63_root_middle_k_odd
      tm63_middle_root_bound tm63_middle_root_a_pos

/-- A single original-TM2 blank-root run through the first seven decrements
of the second, enormous section. -/
theorem tm63_blank_reaches_after_middle7 :
    run tm2 (tm63AfterFirstResetMoves+tm63MiddleFirst7Moves) blank =
      some (s1Config tm63Length1 (8*tm63RootMiddleK) 1
        tm63MiddleAfter7A 0 tm63MiddleAfter7B tm63MiddleAfter7Head) := by
  rw [run_add,tm63_blank_reaches_after_first_reset]
  simp only [Option.bind_some]
  exact tm63_middle_first7_root_source

/-- A single original-TM2 blank-root run through the first eight decrements
of the second section, including the root-specific odd-k (0,1) row. -/
theorem tm63_blank_reaches_after_middle8 :
    run tm2 (tm63AfterFirstResetMoves+tm63MiddleFirst8Moves) blank =
      some (s1Config tm63Length1 (8*tm63RootMiddleK-1) 0
        tm63MiddleAfter8A 0 tm63MiddleAfter8B tm63MiddleAfter8Head) := by
  rw [run_add,tm63_blank_reaches_after_first_reset]
  simp only [Option.bind_some]
  exact tm63_middle_first8_root_source

#print axioms tm63_middle_first7_source
#print axioms tm63_middle_first8_source
#print axioms tm63_middle_first7_root_source
#print axioms tm63_middle_first8_root_source
#print axioms tm63_blank_reaches_after_middle7
#print axioms tm63_blank_reaches_after_middle8

end BB6Coverage.Agent42MiddleSectionCountdown
