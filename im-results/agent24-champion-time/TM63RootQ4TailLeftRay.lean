import TM63RootQ4Tail
import Q4TailToS0Frame
import S0DrainQ4Postlude
import Lean.Elab.Tactic.Omega

/-!
# Authentic P2 q4Tail left-ray adapter input

This isolates the source-specific left side of Agent 42's generic
q4Tail-to-S0 adapter. The root q4Tail frame and its transition itinerary
are imported unchanged from Agent 38. The proof tracks the actual
second 34-frame overwrite and the untouched S0 tail; it does not assume a
blank left exterior.

This is an intermediate source draft. It has not been locally compiled
or axiom-audited in this invocation.
-/

namespace BB6Coverage.Agent24RootQ4TailLeftRay

open BB6Coverage
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42FirstQ4P1Arithmetic
open BB6Coverage.Agent42PositiveZFirstCycleS0Input
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZFirstCycleEndpoint
open BB6Coverage.Agent48PositiveZSecondCyclePrefix
open BB6Coverage.Agent48RootSecondQ4Frame
open BB6Coverage.Agent38RootQ4Tail
open BB6Coverage.Agent44P2Postlude

set_option maxHeartbeats 4000000

def rootSecondQ4TailM : Nat :=
  3*2^rootMarker1Z + 3*rootMarker1Z + 7

def rootSecondQ4TailN : Nat :=
  2^(2^rootMarker1Z-1)

/-- The actual S0 source tail before the first-cycle sweep. -/
def rootSecondQ4Tail0 : List Bool :=
  List.replicate 4 true ++
    binDec (firstQ4P1Width tm63Length1 rootMarker1A)
      (firstQ4P1Value tm63Length1 rootMarker1A) ++ lh

/-- The six cells written by the authentic second 34-step frame, followed
by the exact untouched tail of the original S0 source word. -/
def rootSecondQ4Tail1 : List Bool :=
  [true,false,false,true,true,true] ++ rootSecondQ4Tail0.drop 6

/-- The S0 residual word required by the generic P2 adapter. -/
def rootSecondQ4TailEll : List Bool :=
  p2ResidualLeft rootSecondQ4TailM rootSecondQ4Tail1

def rootSecondQ4TailH : Int :=
  (rootSecondQ4TailM:Int) + 7

def rootSecondQ4TailT1 : Int → Bool :=
  (frameAt rootSecondQ4Frame.tape 1
    secondCyclePrefix34Inside secondCyclePrefix34End).tape

def rootSecondQ4TailT2 : Int → Bool :=
  afterFirstCycleTwoZero rootSecondQ4TailT1
    ((rootSecondQ4TailM:Int)+5)

def rootSecondQ4TailSource : Config :=
  firstCycleS0DrainOutput rootMarker1Z rootSecondQ4Tail0

def rootSecondQ4TailSweepCount : Nat :=
  3*(2^rootMarker1Z-1) + 3*rootMarker1Z + 7

def rootSecondQ4TailSweptTape : Int → Bool :=
  sweptLeft rootSecondQ4TailSweepCount
    rootSecondQ4TailSource.tape (rootSecondQ4TailM:Int)

private theorem sideBit_replicate_true_local
    (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'

private theorem sideBit_drop_local
    (xs : List Bool) (n i : Nat) :
    sideBit (xs.drop n) i = sideBit xs (n+i) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
      cases xs with
      | nil => simp [sideBit]
      | cons b xs =>
          have hidx : Nat.succ n + i = Nat.succ (n+i) := by omega
          simpa [List.drop, sideBit, hidx] using ih xs i

private theorem p2ResidualLeft_leading_local
    (m : Nat) (tail : List Bool) (i : Nat) (hi : i<m+2) :
    sideBit (p2ResidualLeft m tail) i = true := by
  unfold p2ResidualLeft
  rw [Agent6Q4Prefix.sideBit_append_left
    (List.replicate (m+2) true)
    ([false,true,false,false] ++ tail) i (by simp)]
  exact sideBit_replicate_true_local (m+2) i hi

private theorem p2ResidualLeft_boundary_local
    (m : Nat) (tail : List Bool) (j : Nat) (hj : j<4) :
    sideBit (p2ResidualLeft m tail) (m+2+j) =
      sideBit [false,true,false,false] j := by
  unfold p2ResidualLeft
  rw [Agent6Q4Prefix.sideBit_append_right
    (List.replicate (m+2) true)
    ([false,true,false,false] ++ tail) (m+2+j)
    (by simp [List.length_replicate]; omega)]
  have hidx : m+2+j-(List.replicate (m+2) true).length = j := by
    simp [List.length_replicate]
    omega
  rw [hidx, Agent6Q4Prefix.sideBit_append]
  simp [hj, sideBit]

private theorem p2ResidualLeft_tail_local
    (m : Nat) (tail : List Bool) (j : Nat) :
    sideBit (p2ResidualLeft m tail) (m+6+j) =
      sideBit tail j := by
  unfold p2ResidualLeft
  rw [Agent6Q4Prefix.sideBit_append_right
    (List.replicate (m+2) true)
    ([false,true,false,false] ++ tail) (m+6+j)
    (by simp [List.length_replicate]; omega)]
  have hidx : m+6+j-(List.replicate (m+2) true).length = 4+j := by
    simp [List.length_replicate]
    omega
  rw [hidx]
  rw [Agent6Q4Prefix.sideBit_append_right
    [false,true,false,false] tail (4+j) (by simp)]
  have hidx' : 4+j-[false,true,false,false].length = j := by
    simp
  rw [hidx']

private theorem rootSecondQ4Tail1_firstSix
    (j : Nat) (hj : j<6) :
    sideBit rootSecondQ4Tail1 j =
      sideBit [true,false,false,true,true,true] j := by
  unfold rootSecondQ4Tail1
  rw [Agent6Q4Prefix.sideBit_append_left
    [true,false,false,true,true,true] (rootSecondQ4Tail0.drop 6)
    j (by simp)]

private theorem rootSecondQ4Tail1_afterSix
    (j : Nat) :
    sideBit rootSecondQ4Tail1 (6+j) =
      sideBit rootSecondQ4Tail0 (6+j) := by
  unfold rootSecondQ4Tail1
  rw [Agent6Q4Prefix.sideBit_append_right
    [true,false,false,true,true,true] (rootSecondQ4Tail0.drop 6)
    (6+j) (by simp)]
  have hidx : 6+j-[true,false,false,true,true,true].length = j := by
    simp
  rw [hidx]
  exact sideBit_drop_local rootSecondQ4Tail0 6 j

private theorem rootSecondQ4TailEll_afterTwelve
    (j : Nat) :
    sideBit rootSecondQ4TailEll (rootSecondQ4TailM+12+j) =
      sideBit rootSecondQ4Tail0 (6+j) := by
  calc
    sideBit rootSecondQ4TailEll (rootSecondQ4TailM+12+j)
        = sideBit rootSecondQ4Tail1 (6+j) := by
            simpa [rootSecondQ4TailEll] using
              p2ResidualLeft_tail_local rootSecondQ4TailM
                rootSecondQ4Tail1 (6+j)
    _ = sideBit rootSecondQ4Tail0 (6+j) :=
      rootSecondQ4Tail1_afterSix j

private theorem s0LeftSweep_eq_sweptLeft_local
    (n : Nat) (T : Int → Bool) (h : Int) :
    s0LeftSweep n T h = sweptLeft n T h := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hmicro : afterS0LeftOne T h = holeThree T h := by
        funext x
        by_cases hx0 : x=h
        · subst x
          simp [afterS0LeftOne,holeThree]
        · by_cases hx1 : x=h+1
          · subst x
            simp [afterS0LeftOne,holeThree]
          · simp [afterS0LeftOne,holeThree,hx0,hx1]
      simpa [s0LeftSweep,sweptLeft,hmicro] using
        ih (afterS0LeftOne T h) (h-1)

private theorem rootSecondQ4TailSweep_profile :
    ∀ x : Int,
      rootSecondQ4TailSweptTape x =
        if x=4 then false
        else if (5:Int)≤x ∧ x≤(rootSecondQ4TailM:Int)+1 then true
        else rootSecondQ4TailSource.tape x := by
  have hHk :
      (rootSecondQ4TailM:Int) -
        (rootSecondQ4TailSweepCount:Int) = 3 := by
    dsimp [rootSecondQ4TailM,rootSecondQ4TailSweepCount]
    omega
  have hkpos : 0 < rootSecondQ4TailSweepCount := by
    dsimp [rootSecondQ4TailSweepCount]
    have hp : 0 < 2^rootMarker1Z := Nat.pow_pos (by decide)
    omega
  have hSweep :
      rootSecondQ4TailSweptTape =
        s0LeftSweep rootSecondQ4TailSweepCount
          rootSecondQ4TailSource.tape (rootSecondQ4TailM:Int) := by
    dsimp [rootSecondQ4TailSweptTape]
    exact (s0LeftSweep_eq_sweptLeft_local
      rootSecondQ4TailSweepCount rootSecondQ4TailSource.tape
      (rootSecondQ4TailM:Int)).symm
  have hshift := s0LeftSweep_shift rootSecondQ4TailSweepCount
    rootSecondQ4TailSource.tape (rootSecondQ4TailM:Int) hkpos
  intro x
  rw [hSweep]
  have hx := hshift x
  simpa [hHk] using hx

private theorem rootSecondQ4Frame_eq_sweptFrame :
    rootSecondQ4Frame =
      frameAt rootSecondQ4TailSweptTape 3
        firstCyclePostludeInside firstCyclePostludeEnd := by
  rfl

private theorem rootSecondQ4Frame_tape_eq_swept
    (x : Int)
    (hout : firstCyclePostludeInside (x-3)=false) :
    rootSecondQ4Frame.tape x = rootSecondQ4TailSweptTape x := by
  rw [rootSecondQ4Frame_eq_sweptFrame]
  rw [frameAt_tape]
  simp [hout]

private theorem rootSecondQ4TailSource_right_cell
    (j : Nat) :
    rootSecondQ4TailSource.tape
      ((rootSecondQ4TailM:Int)+1+(j:Int)) =
      sideBit (s0RightFacing (2^rootMarker1Z-1)) j := by
  have hcell := s0Config_right_cell
    (firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0)
    (2^rootMarker1Z-1) 0
    (2^(2^rootMarker1Z-1)-1)
    (rootSecondQ4TailM:Int) j
  simpa [rootSecondQ4TailSource,firstCycleS0DrainOutput,
    rootSecondQ4TailM] using hcell

/-- The authentic first-cycle q4 checkpoint has the full rightward
one-run needed by the second 34-step prefix. This extracts the local
linearRightOnes V 5 m fact used privately in Agent 24's original
composition. -/
theorem rootSecondQ4Frame_linearRightOnes :
    linearRightOnes rootSecondQ4Frame.tape 5 rootSecondQ4TailM := by
  intro i hi
  let x : Int := 5+(i:Int)
  have hxlo : 5≤x := by dsimp [x]; omega
  have hxhi : x≤(rootSecondQ4TailM:Int)+4 := by
    dsimp [x]
    omega
  have hout : firstCyclePostludeInside (x-3)=false := by
    simp [firstCyclePostludeInside,x]
    omega
  have hframe := rootSecondQ4Frame_tape_eq_swept x hout
  have hprofile := rootSecondQ4TailSweep_profile x
  by_cases hx : x≤(rootSecondQ4TailM:Int)+1
  · have hneq : x≠4 := by omega
    have hmid : (5:Int)≤x ∧ x≤(rootSecondQ4TailM:Int)+1 :=
      ⟨hxlo,hx⟩
    rw [hframe,hprofile]
    simp [hneq,hmid]
  · have hcases :
        x=(rootSecondQ4TailM:Int)+2 ∨
        x=(rootSecondQ4TailM:Int)+3 ∨
        x=(rootSecondQ4TailM:Int)+4 := by omega
    have hsource : rootSecondQ4TailSource.tape x = true := by
      rcases hcases with h|h|h
      · subst x
        have hc := rootSecondQ4TailSource_right_cell 1
        have hcoord :
            (rootSecondQ4TailM:Int)+1+(1:Int) =
              (rootSecondQ4TailM:Int)+2 := by omega
        rw [hcoord] at hc
        simpa [s0RightFacing,sideBit] using hc
      · subst x
        have hc := rootSecondQ4TailSource_right_cell 2
        have hcoord :
            (rootSecondQ4TailM:Int)+1+(2:Int) =
              (rootSecondQ4TailM:Int)+3 := by omega
        rw [hcoord] at hc
        simpa [s0RightFacing,sideBit] using hc
      · subst x
        have hc := rootSecondQ4TailSource_right_cell 3
        have hcoord :
            (rootSecondQ4TailM:Int)+1+(3:Int) =
              (rootSecondQ4TailM:Int)+4 := by omega
        rw [hcoord] at hc
        simpa [s0RightFacing,sideBit] using hc
    have hneq : x≠4 := by omega
    have hnot :
        ¬ ((5:Int)≤x ∧ x≤(rootSecondQ4TailM:Int)+1) := by omega
    rw [hframe,hprofile]
    simp [hneq,hnot,hsource]

/-- The unmodified far-left exterior of the first-cycle q4 frame is exactly
the original S0 source tail after the six cells written by the 34-frame. -/
theorem rootSecondQ4Frame_leftTail
    (j : Nat) :
    rootSecondQ4Frame.tape (-7-(j:Int)) =
      sideBit rootSecondQ4Tail0 (6+j) := by
  let x : Int := -7-(j:Int)
  have hout : firstCyclePostludeInside (x-3)=false := by
    simp [firstCyclePostludeInside,x]
    omega
  have hframe := rootSecondQ4Frame_tape_eq_swept x hout
  have hprofile := rootSecondQ4TailSweep_profile x
  have hneq : x≠4 := by dsimp [x]; omega
  have hnot :
      ¬ ((5:Int)≤x ∧ x≤(rootSecondQ4TailM:Int)+1) := by
    dsimp [x]
    omega
  have hsource :
      rootSecondQ4TailSweptTape x = rootSecondQ4TailSource.tape x := by
    rw [hprofile]
    simp [hneq,hnot]
  have hleftFacing :
      s0LeftFacing
        (firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0)
        (2^rootMarker1Z-1) 0 =
        d1pow (2^rootMarker1Z-1) ++
          firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0 := by
    simp [s0LeftFacing,binDec_zero]
  have hcell := s0Config_left_cell
    (firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0)
    (2^rootMarker1Z-1) 0
    (2^(2^rootMarker1Z-1)-1)
    (rootSecondQ4TailM:Int) (rootSecondQ4TailM+7+j)
  rw [hleftFacing] at hcell
  have hcoord :
      (rootSecondQ4TailM:Int) -
        ((rootSecondQ4TailM+7+j:Int)) = x := by
    dsimp [x]
    omega
  rw [hcoord] at hcell
  have htail :
      sideBit
        (d1pow (2^rootMarker1Z-1) ++
          firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0)
        (rootSecondQ4TailM+7+j) =
        sideBit rootSecondQ4Tail0 (6+j) := by
    rw [Agent6Q4Prefix.sideBit_append_right
      (d1pow (2^rootMarker1Z-1))
      (firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0)
      (rootSecondQ4TailM+7+j)
      (by rw [d1pow_length]; dsimp [rootSecondQ4TailM]; omega)]
    rw [d1pow_length]
    have hidx :
        rootSecondQ4TailM+7+j - 3*(2^rootMarker1Z-1) =
          3*rootMarker1Z+17+j := by
      dsimp [rootSecondQ4TailM]
      omega
    rw [hidx]
    unfold firstCycleResidualLeft
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (3*rootMarker1Z+7) true)
      ([false,true,false,false] ++ rootSecondQ4Tail0)
      (3*rootMarker1Z+17+j)
      (by simp [List.length_replicate]; omega)]
    rw [List.length_replicate]
    have hidx' :
        3*rootMarker1Z+17+j-(3*rootMarker1Z+7) = 10+j := by omega
    rw [hidx']
    rw [Agent6Q4Prefix.sideBit_append_right
      [false,true,false,false] rootSecondQ4Tail0 (10+j) (by simp)]
    have hidx'' :
        10+j-[false,true,false,false].length = 6+j := by
      simp
    rw [hidx'']
  calc
    rootSecondQ4Frame.tape x = rootSecondQ4TailSweptTape x := hframe
    _ = rootSecondQ4TailSource.tape x := hsource
    _ = sideBit
        (d1pow (2^rootMarker1Z-1) ++
          firstCycleResidualLeft rootMarker1Z rootSecondQ4Tail0)
        (rootSecondQ4TailM+7+j) := by
          simpa [rootSecondQ4TailSource,firstCycleS0DrainOutput,
            rootSecondQ4TailM] using hcell
    _ = sideBit rootSecondQ4Tail0 (6+j) := htail

private theorem rootSecondQ4TailT1_after
    (x : Int) (hx : 5≤x) :
    rootSecondQ4TailT1 x = rootSecondQ4Frame.tape x := by
  dsimp [rootSecondQ4TailT1]
  rw [frameAt_tape]
  have hnot : secondCyclePrefix34Inside (x-1)=false := by
    simp [secondCyclePrefix34Inside]
    omega
  simp [hnot]

private theorem rootSecondQ4TailT1_before
    (x : Int) (hx : x≤-7) :
    rootSecondQ4TailT1 x = rootSecondQ4Frame.tape x := by
  dsimp [rootSecondQ4TailT1]
  rw [frameAt_tape]
  have hnot : secondCyclePrefix34Inside (x-1)=false := by
    simp [secondCyclePrefix34Inside]
    omega
  simp [hnot]

private theorem rootSecondQ4TailT1_boundary
    (j : Nat) (hj : j<4) :
    rootSecondQ4TailT1 (3-(j:Int)) =
      sideBit [false,true,false,false] j := by
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with
    h|h|h|h <;> subst j <;>
      simp [rootSecondQ4TailT1,frameAt_tape,
        secondCyclePrefix34Inside,secondCyclePrefix34End,sideBit]

private theorem rootSecondQ4TailT1_six
    (j : Nat) (hj : j<6) :
    rootSecondQ4TailT1 (-1-(j:Int)) =
      sideBit [true,false,false,true,true,true] j := by
  rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 by omega) with
    h|h|h|h|h|h <;> subst j <;>
      simp [rootSecondQ4TailT1,frameAt_tape,
        secondCyclePrefix34Inside,secondCyclePrefix34End,sideBit]

private theorem rootSecondQ4TailT2_eq_T1
    (x : Int)
    (h0 : x≠(rootSecondQ4TailM:Int)+5)
    (h1 : x≠(rootSecondQ4TailM:Int)+6) :
    rootSecondQ4TailT2 x = rootSecondQ4TailT1 x := by
  simp [rootSecondQ4TailT2,afterFirstCycleTwoZero,h0,h1]

private theorem rootSecondQ4TailT2_setup :
    rootSecondQ4TailT2 ((rootSecondQ4TailM:Int)+5) = true ∧
    rootSecondQ4TailT2 ((rootSecondQ4TailM:Int)+6) = true := by
  constructor <;>
    simp [rootSecondQ4TailT2,afterFirstCycleTwoZero]

/-- The left-neighbor guard for Agent 42's q4Tail-to-S0 adapter is exactly
the second cell written by the two-zero setup. -/
theorem rootSecondQ4Tail_leftGuard :
    rootSecondQ4TailT2 (rootSecondQ4TailH-1) = true := by
  have hcoord :
      rootSecondQ4TailH-1 = (rootSecondQ4TailM:Int)+6 := by
    dsimp [rootSecondQ4TailH]
    omega
  rw [hcoord]
  exact rootSecondQ4TailT2_setup.2

/-- The authentic second-prefix tail begins with 100, the exact guard
required by Agent 44's corrected S0 drain/postlude. -/
theorem rootSecondQ4Tail_tail100 :
    sideBit rootSecondQ4Tail1 0 = true ∧
    sideBit rootSecondQ4Tail1 1 = false ∧
    sideBit rootSecondQ4Tail1 2 = false := by
  simp [rootSecondQ4Tail1,sideBit]

/-- Complete authentic left-facing source ray for the generic q4Tail
adapter. The proof distinguishes the two-zero setup, the E-scan one-run,
the 0100/100111 overwritten frame cells, and the exact original S0 tail. -/
theorem rootSecondQ4Tail_leftResidual :
    ∀ i : Nat,
      rootSecondQ4TailT2
        (rootSecondQ4TailH-2-(i:Int)) =
      sideBit rootSecondQ4TailEll i := by
  intro i
  have hcoord :
      rootSecondQ4TailH-2-(i:Int) =
        (rootSecondQ4TailM:Int)+5-(i:Int) := by
    dsimp [rootSecondQ4TailH]
    omega
  rw [hcoord]
  by_cases hi0 : i=0
  · subst i
    have hT := rootSecondQ4TailT2_setup.1
    have hS := p2ResidualLeft_leading_local
      rootSecondQ4TailM rootSecondQ4Tail1 0 (by omega)
    exact hT.trans hS.symm
  · by_cases hiLead : i≤rootSecondQ4TailM+1
    · by_cases hiLast : i=rootSecondQ4TailM+1
      · have hx :
          (rootSecondQ4TailM:Int)+5-(i:Int)=4 := by omega
        rw [hx]
        have hT2 := rootSecondQ4TailT2_eq_T1 4 (by omega) (by omega)
        have hT1 :
            rootSecondQ4TailT1 4 = true := by
          simp [rootSecondQ4TailT1,frameAt_tape,
            secondCyclePrefix34Inside,secondCyclePrefix34End]
        have hS := p2ResidualLeft_leading_local
          rootSecondQ4TailM rootSecondQ4Tail1 i (by omega)
        exact hT2.trans (hT1.trans hS.symm)
      · have hiLE : i≤rootSecondQ4TailM := by omega
        let j : Nat := rootSecondQ4TailM-i
        have hj : j<rootSecondQ4TailM := by
          dsimp [j]
          omega
        have hx :
            (rootSecondQ4TailM:Int)+5-(i:Int) =
              5+(j:Int) := by
          dsimp [j]
          omega
        rw [hx]
        have hT2 := rootSecondQ4TailT2_eq_T1
          (5+(j:Int)) (by omega) (by omega)
        have hT1 := rootSecondQ4TailT1_after
          (5+(j:Int)) (by omega)
        have hfirst := rootSecondQ4Frame_linearRightOnes j hj
        have hS := p2ResidualLeft_leading_local
          rootSecondQ4TailM rootSecondQ4Tail1 i (by omega)
        calc
          rootSecondQ4TailT2 (5+(j:Int)) =
              rootSecondQ4TailT1 (5+(j:Int)) := hT2
          _ = rootSecondQ4Frame.tape (5+(j:Int)) := hT1
          _ = true := hfirst
          _ = sideBit rootSecondQ4TailEll i := hS.symm
    · by_cases hiBoundary : i≤rootSecondQ4TailM+5
      · have hcases :
          i=rootSecondQ4TailM+2 ∨
          i=rootSecondQ4TailM+3 ∨
          i=rootSecondQ4TailM+4 ∨
          i=rootSecondQ4TailM+5 := by omega
        rcases hcases with h|h|h|h
        · subst i
          have hx :
              (rootSecondQ4TailM:Int)+5-(i:Int)=3 := by omega
          rw [hx]
          have hT2 := rootSecondQ4TailT2_eq_T1 3 (by omega) (by omega)
          have hT1 := rootSecondQ4TailT1_boundary 0 (by omega)
          have hS := p2ResidualLeft_boundary_local
            rootSecondQ4TailM rootSecondQ4Tail1 0 (by omega)
          exact hT2.trans (hT1.trans hS.symm)
        · subst i
          have hx :
              (rootSecondQ4TailM:Int)+5-(i:Int)=2 := by omega
          rw [hx]
          have hT2 := rootSecondQ4TailT2_eq_T1 2 (by omega) (by omega)
          have hT1 := rootSecondQ4TailT1_boundary 1 (by omega)
          have hS := p2ResidualLeft_boundary_local
            rootSecondQ4TailM rootSecondQ4Tail1 1 (by omega)
          exact hT2.trans (hT1.trans hS.symm)
        · subst i
          have hx :
              (rootSecondQ4TailM:Int)+5-(i:Int)=1 := by omega
          rw [hx]
          have hT2 := rootSecondQ4TailT2_eq_T1 1 (by omega) (by omega)
          have hT1 := rootSecondQ4TailT1_boundary 2 (by omega)
          have hS := p2ResidualLeft_boundary_local
            rootSecondQ4TailM rootSecondQ4Tail1 2 (by omega)
          exact hT2.trans (hT1.trans hS.symm)
        · subst i
          have hx :
              (rootSecondQ4TailM:Int)+5-(i:Int)=0 := by omega
          rw [hx]
          have hT2 := rootSecondQ4TailT2_eq_T1 0 (by omega) (by omega)
          have hT1 := rootSecondQ4TailT1_boundary 3 (by omega)
          have hS := p2ResidualLeft_boundary_local
            rootSecondQ4TailM rootSecondQ4Tail1 3 (by omega)
          exact hT2.trans (hT1.trans hS.symm)
      · by_cases hiSix : i≤rootSecondQ4TailM+11
        · obtain ⟨j,hj,hidx⟩ :
            ∃ j : Nat, j<6 ∧ i=rootSecondQ4TailM+6+j := by
            refine ⟨i-(rootSecondQ4TailM+6), ?_, ?_⟩ <;> omega
          rw [hidx]
          have hx :
              (rootSecondQ4TailM:Int)+5-
                ((rootSecondQ4TailM+6+j:Int)) =
                -1-(j:Int) := by omega
          rw [hx]
          have hT2 := rootSecondQ4TailT2_eq_T1
            (-1-(j:Int)) (by omega) (by omega)
          have hT1 := rootSecondQ4TailT1_six j hj
          have hS0 := p2ResidualLeft_tail_local
            rootSecondQ4TailM rootSecondQ4Tail1 j
          have hS1 := rootSecondQ4Tail1_firstSix j hj
          have hS :
              sideBit rootSecondQ4TailEll
                (rootSecondQ4TailM+6+j) =
                sideBit [true,false,false,true,true,true] j :=
            hS0.trans hS1
          calc
            rootSecondQ4TailT2 (-1-(j:Int)) =
                rootSecondQ4TailT1 (-1-(j:Int)) := hT2
            _ = sideBit [true,false,false,true,true,true] j := hT1
            _ = sideBit rootSecondQ4TailEll
                (rootSecondQ4TailM+6+j) := hS.symm
        · have hiGe : rootSecondQ4TailM+12≤i := by omega
          let j : Nat := i-(rootSecondQ4TailM+12)
          have hidx : i=rootSecondQ4TailM+12+j := by
            dsimp [j]
            omega
          rw [hidx]
          have hx :
              (rootSecondQ4TailM:Int)+5-
                ((rootSecondQ4TailM+12+j:Int)) =
                -7-(j:Int) := by omega
          rw [hx]
          have hT2 := rootSecondQ4TailT2_eq_T1
            (-7-(j:Int)) (by omega) (by omega)
          have hT1 := rootSecondQ4TailT1_before
            (-7-(j:Int)) (by omega)
          have hframe := rootSecondQ4Frame_leftTail j
          have hS := rootSecondQ4TailEll_afterTwelve j
          calc
            rootSecondQ4TailT2 (-7-(j:Int)) =
                rootSecondQ4TailT1 (-7-(j:Int)) := hT2
            _ = rootSecondQ4Frame.tape (-7-(j:Int)) := hT1
            _ = sideBit rootSecondQ4Tail0 (6+j) := hframe
            _ = sideBit rootSecondQ4TailEll
                (rootSecondQ4TailM+12+j) := hS.symm

#print axioms rootSecondQ4Frame_linearRightOnes
#print axioms rootSecondQ4Frame_leftTail
#print axioms rootSecondQ4Tail_leftGuard
#print axioms rootSecondQ4Tail_leftResidual

end BB6Coverage.Agent24RootQ4TailLeftRay
