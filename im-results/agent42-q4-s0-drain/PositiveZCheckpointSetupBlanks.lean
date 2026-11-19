import PositiveZCheckpointSetupComposition
import Agent6Q4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Exterior blank-tail lemmas for the positive-z setup prefix

The setup suffix currently assumes a blank left tail before B20 and a
blank right tail beyond the incoming z counter.  Both conditions are
inherited from the explicit initial S0 encoder after the two left
sweeps and the B8 frame: all three operations have finite support strictly
inside those exterior regions.

This module proves the two blank-tail conditions directly, without
assuming any of the local SetupSuffixGuards.
-/

namespace BB6Coverage.Agent42PositiveZSetupBlanks

open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48PositiveZSetup
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent6Q4Prefix

/-- A left sweep changes only cells from its final head onward. -/
theorem sweptLeft_preserves_before (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h-(n:Int)+1) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      simp only [sweptLeft]
      have hx' : x < (h-1)-(n:Int)+1 := by omega
      rw [ih (holeThree T h) (h-1) x hx']
      have hx1 : x ≠ h+1 := by omega
      have hx0 : x ≠ h := by omega
      simp [holeThree,hx1,hx0]

/-- A left sweep changes no cell strictly to the right of its initial
head plus one. -/
theorem sweptLeft_preserves_after (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h+1 < x) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      simp only [sweptLeft]
      have hx' : (h-1)+1 < x := by omega
      rw [ih (holeThree T h) (h-1) x hx']
      have hx1 : x ≠ h+1 := by omega
      have hx0 : x ≠ h := by omega
      simp [holeThree,hx1,hx0]

def setupPrefixInputTape (L A z : Nat) : Int → Bool :=
  (s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0).tape

/-- Tape after the first (3*A+1)-cell left sweep, B8, and the second
(3*L+5)-cell left sweep. -/
def setupPrefixAfterScans (L A z : Nat) : Int → Bool :=
  sweptLeft (3*L+5)
    (q4FrameAt
      (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
      (-(3*A+1:Int)) setupB8Inside setupB8End).tape
    (-(3*A+3:Int))

def setupPrefixHead (A L : Nat) : Int :=
  -(3*A+3*L+8:Int)

/-- The initial S0 encoder has no support strictly left of the
B20-prefix blank boundary. -/
theorem setupPrefixInput_left_blank (L A z : Nat) (x : Int)
    (hx : x < -(3*A+3*L+13:Int)) :
    setupPrefixInputTape L A z x = false := by
  let i : Nat := Int.toNat (-x)
  have hi : (i:Int) = -x := by
    dsimp [i]
    exact Int.toNat_of_nonneg (by omega)
  have hcoord : (0:Int) - (i:Int) = x := by omega
  have hcell := s0Config_left_cell
    (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 i
  rw [hcoord] at hcell
  have hleft :
      s0LeftFacing (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 =
        d1pow A ++ (markerWord 1 ++ d0 ++ d1pow L ++ lh) := by
    simp [s0LeftFacing, binDec_zero]
  rw [hleft] at hcell
  have hlen :
      (d1pow A ++ (markerWord 1 ++ d0 ++ d1pow L ++ lh)).length =
        3*A+3*L+12 := by
    simp [d1pow_length, markerWord, d0, lh, List.append_assoc]
  have hidx :
      (d1pow A ++ (markerWord 1 ++ d0 ++ d1pow L ++ lh)).length ≤ i := by
    rw [hlen]
    omega
  calc
    setupPrefixInputTape L A z x =
        sideBit
          (d1pow A ++ (markerWord 1 ++ d0 ++ d1pow L ++ lh)) i := by
            simpa [setupPrefixInputTape] using hcell
    _ = false := sideBit_ge_length _ _ hidx

/-- The initial S0 encoder's right-facing support ends exactly at
cell 3*z+9. -/
theorem setupPrefixInput_right_blank (L A z : Nat) (x : Int)
    (hx : 3*z+9 < x) :
    setupPrefixInputTape L A z x = false := by
  let i : Nat := Int.toNat (x-1)
  have hi : (i:Int) = x-1 := by
    dsimp [i]
    exact Int.toNat_of_nonneg (by omega)
  have hcoord : (0:Int)+1+(i:Int) = x := by omega
  have hcell := s0Config_right_cell
    (markerWord 1 ++ d0 ++ d1pow L ++ lh) A 0 z 0 i
  rw [hcoord] at hcell
  have hlen : (s0RightFacing z).length = 3*z+9 := by
    simp [s0RightFacing, d1pow_length]
  have hidx : (s0RightFacing z).length ≤ i := by
    rw [hlen]
    omega
  calc
    setupPrefixInputTape L A z x =
        sideBit (s0RightFacing z) i := by
          simpa [setupPrefixInputTape] using hcell
    _ = false := sideBit_ge_length _ _ hidx

/-- The two left sweeps and B8 preserve the required blank prefix. -/
theorem setupPrefixAfterScans_leftBlank (L A z : Nat) :
    SetupPrefixLeftBlank (setupPrefixAfterScans L A z)
      (setupPrefixHead A L) := by
  intro x hx
  have hx0 : x < -(3*A+3*L+13:Int) := by
    simpa [SetupPrefixLeftBlank, setupPrefixHead] using hx
  have hfirst :
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x =
        setupPrefixInputTape L A z x := by
    apply sweptLeft_preserves_before
    omega
  have hb8 :
      (q4FrameAt
        (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
        (-(3*A+1:Int)) setupB8Inside setupB8End).tape x =
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x := by
    rw [q4FrameAt_tape]
    have hnot : setupB8Inside (x-(-(3*A+1:Int))) = false := by
      simp [setupB8Inside]
      omega
    simp [hnot]
  have hsecond :
      sweptLeft (3*L+5)
        (q4FrameAt
          (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
          (-(3*A+1:Int)) setupB8Inside setupB8End).tape
        (-(3*A+3:Int)) x =
      (q4FrameAt
          (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
          (-(3*A+1:Int)) setupB8Inside setupB8End).tape x := by
    apply sweptLeft_preserves_before
    omega
  change
    sweptLeft (3*L+5)
      (q4FrameAt
        (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
        (-(3*A+1:Int)) setupB8Inside setupB8End).tape
      (-(3*A+3:Int)) x = false
  rw [hsecond,hb8,hfirst]
  exact setupPrefixInput_left_blank L A z x hx0

/-- The two left sweeps and B8 preserve the required blank right tail. -/
theorem setupPrefixAfterScans_rightBlank (L A z : Nat) :
    SetupPrefixRightBlank (setupPrefixAfterScans L A z)
      (setupPrefixHead A L) A L z := by
  intro x hx
  have hx0 : 3*z+9 < x := by
    dsimp [SetupPrefixRightBlank, setupPrefixHead] at hx
    omega
  have hfirst :
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x =
        setupPrefixInputTape L A z x := by
    apply sweptLeft_preserves_after
    omega
  have hb8 :
      (q4FrameAt
        (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
        (-(3*A+1:Int)) setupB8Inside setupB8End).tape x =
      sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0 x := by
    rw [q4FrameAt_tape]
    have hnot : setupB8Inside (x-(-(3*A+1:Int))) = false := by
      simp [setupB8Inside]
      omega
    simp [hnot]
  have hsecond :
      sweptLeft (3*L+5)
        (q4FrameAt
          (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
          (-(3*A+1:Int)) setupB8Inside setupB8End).tape
        (-(3*A+3:Int)) x =
      (q4FrameAt
          (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
          (-(3*A+1:Int)) setupB8Inside setupB8End).tape x := by
    apply sweptLeft_preserves_after
    omega
  change
    sweptLeft (3*L+5)
      (q4FrameAt
        (sweptLeft (3*A+1) (setupPrefixInputTape L A z) 0)
        (-(3*A+1:Int)) setupB8Inside setupB8End).tape
      (-(3*A+3:Int)) x = false
  rw [hsecond,hb8,hfirst]
  exact setupPrefixInput_right_blank L A z x hx0

#print axioms sweptLeft_preserves_before
#print axioms sweptLeft_preserves_after
#print axioms setupPrefixInput_left_blank
#print axioms setupPrefixInput_right_blank
#print axioms setupPrefixAfterScans_leftBlank
#print axioms setupPrefixAfterScans_rightBlank

end BB6Coverage.Agent42PositiveZSetupBlanks
