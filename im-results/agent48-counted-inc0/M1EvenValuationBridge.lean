import ChampionRootBridge
import M1EvenState1Sweep
import M1EvenState5Sweep
import CountedSweep
import Lean.Elab.Tactic.Omega

/-!
# Uniform two-sided M1-even valuation bridge

This isolates the exact source-machine bridge after the six-step
state-3-to-state-1 prelude.  If the state-1 head is blank, there are
3(v+1)+1 ones to its left, the next two cells are zero, and the
right-hand boundary is 0,1,1,1, then a left-hole sweep followed by the
matching right-hole sweep reaches state 4 at h+5 in 12v+23 moves.

The left and right sweeps are the independent counted source lemmas in
M1EvenState1Sweep.lean and M1EvenState5Sweep.lean.  This file contains
only the finite transitions and their exact composition.
-/

namespace BB6Coverage.Agent48M1EvenValuationBridge

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48M1EvenValuationSweep
open BB6Coverage.Agent24M1EvenValuationBridge

/-- Local simp interface for the source table. The upstream table matches
on Fin.val; simp does not normalize numeral Fin.vals by itself. -/
@[simp] private theorem tm2_0_0 : tm2 ((0 : Fin 6), false) = some ⟨true,true,1⟩ := by rfl
@[simp] private theorem tm2_0_1 : tm2 ((0 : Fin 6), true) = none := by rfl
@[simp] private theorem tm2_1_0 : tm2 ((1 : Fin 6), false) = some ⟨true,false,2⟩ := by rfl
@[simp] private theorem tm2_1_1 : tm2 ((1 : Fin 6), true) = some ⟨false,true,5⟩ := by rfl
@[simp] private theorem tm2_2_0 : tm2 ((2 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl
@[simp] private theorem tm2_2_1 : tm2 ((2 : Fin 6), true) = some ⟨false,false,3⟩ := by rfl
@[simp] private theorem tm2_3_0 : tm2 ((3 : Fin 6), false) = some ⟨false,false,2⟩ := by rfl
@[simp] private theorem tm2_3_1 : tm2 ((3 : Fin 6), true) = some ⟨true,true,1⟩ := by rfl
@[simp] private theorem tm2_4_0 : tm2 ((4 : Fin 6), false) = some ⟨true,true,0⟩ := by rfl
@[simp] private theorem tm2_4_1 : tm2 ((4 : Fin 6), true) = some ⟨true,true,4⟩ := by rfl
@[simp] private theorem tm2_5_0 : tm2 ((5 : Fin 6), false) = some ⟨true,true,4⟩ := by rfl
@[simp] private theorem tm2_5_1 : tm2 ((5 : Fin 6), true) = some ⟨false,true,3⟩ := by rfl

@[simp] private theorem int_add_neg_one (x : Int) : x + (-1 : Int) = x - 1 := by omega
@[simp] private theorem int_sub_one_sub_one (x : Int) : x - 1 - 1 = x - 2 := by omega
@[simp] private theorem int_sub_two_sub_one (x : Int) : x - 2 - 1 = x - 3 := by omega
@[simp] private theorem int_add_one_add_one (x : Int) : x + 1 + 1 = x + 2 := by omega
@[simp] private theorem int_sub_one_add_one (x : Int) : x - 1 + 1 = x := by omega
@[simp] private theorem int_sub_two_add_one (x : Int) : x - 2 + 1 = x - 1 := by omega
@[simp] private theorem int_sub_three_add_one (x : Int) : x - 3 + 1 = x - 2 := by omega
@[simp] private theorem int_add_one_sub_one (x : Int) : x + 1 - 1 = x := by omega
@[simp] private theorem int_add_two_sub_one (x : Int) : x + 2 - 1 = x + 1 := by omega

/-- After the four-step state-1 exit and three-step state-5 setup. -/
def valuationSetupTape (T : Int → Bool) (x : Int) : Int → Bool :=
  fun y => if y = x then false
    else if y = x-1 then true
    else if y = x-2 then true
    else if y = x-3 then true
    else T y

/-- The four-step state-1-to-state-4 left exit. -/
def valuationExit4Tape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun y => if y = h then true
    else if y = h-1 then false
    else if y = h-2 then false
    else if y = h-3 then true
    else T y

/-- The three-step state-4-to-state-5 right setup. -/
def valuationSetup3Tape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun y => if y = h then true
    else if y = h+1 then true
    else if y = h+2 then false
    else T y

/-- The one-step state-5 exit writes the blank cell and enters state 4. -/
def valuationExit1Tape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun y => if y = h then true else T y

/-- The six-step state-3 prelude writes three ones immediately to
the left and returns to state 1 at the original head. -/
def valuationPreludeTape (T : Int → Bool) (h : Int) : Int → Bool :=
  fun y => if y = h-1 then true
    else if y = h-2 then true
    else if y = h-3 then true
    else T y

theorem valuation_state3_prelude6 (T : Int → Bool) (h : Int)
    (h0 : T h = false)
    (h1 : T (h-1) = true)
    (h2 : T (h-2) = false)
    (h3 : T (h-3) = false) :
    run tm2 6 ⟨3,h,T⟩ =
      some ⟨1,h,valuationPreludeTape T h⟩ := by
  have hne1 : h-1 ≠ h := by omega
  have hne2 : h-2 ≠ h := by omega
  have hne3 : h-3 ≠ h := by omega
  have hne4 : h-2 ≠ h-1 := by omega
  have hne5 : h-3 ≠ h-1 := by omega
  have hne6 : h-3 ≠ h-2 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1, h2, h3,
    hne1, hne2, hne3, hne4, hne5, hne6, valuationPreludeTape]
  funext y
  by_cases hy0 : y = h
  · simp_all [valuationPreludeTape]
  · by_cases hy1 : y = h-1
    · simp_all [valuationPreludeTape]
    · by_cases hy2 : y = h-2
      · simp_all [valuationPreludeTape]
      · by_cases hy3 : y = h-3
        · simp_all [valuationPreludeTape]
        · simp_all [valuationPreludeTape]

theorem valuation_state1_exit4 (T : Int → Bool) (h : Int)
    (h0 : T h = false)
    (h1 : T (h-1) = true)
    (h2 : T (h-2) = false)
    (h3 : T (h-3) = false) :
    run tm2 4 ⟨1,h,T⟩ =
      some ⟨4,h-2,valuationExit4Tape T h⟩ := by
  have hne1 : h-1 ≠ h := by omega
  have hne2 : h-2 ≠ h := by omega
  have hne3 : h-3 ≠ h := by omega
  have hne4 : h-2 ≠ h-1 := by omega
  have hne5 : h-3 ≠ h-1 := by omega
  have hne6 : h-3 ≠ h-2 := by omega
  have hne1' : h ≠ h-1 := by omega
  have hne2' : h ≠ h-2 := by omega
  have hne3' : h ≠ h-3 := by omega
  have hne4' : h-1 ≠ h-2 := by omega
  have hne5' : h-1 ≠ h-3 := by omega
  have hne6' : h-2 ≠ h-3 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1, h2, h3,
    hne1, hne2, hne3, hne4, hne5, hne6,
    hne1', hne2', hne3', hne4', hne5', hne6', valuationExit4Tape]
  funext y
  by_cases hy0 : y = h
  · simp_all [valuationExit4Tape]
  · by_cases hy1 : y = h-1
    · simp_all [valuationExit4Tape]
    · by_cases hy2 : y = h-2
      · simp_all [valuationExit4Tape]
      · by_cases hy3 : y = h-3
        · simp_all [valuationExit4Tape]
        · simp_all [valuationExit4Tape]

theorem valuation_state4_setup3 (T : Int → Bool) (h : Int)
    (h0 : T h = false)
    (h1 : T (h+1) = false)
    (h2 : T (h+2) = true) :
    run tm2 3 ⟨4,h,T⟩ =
      some ⟨5,h+3,valuationSetup3Tape T h⟩ := by
  have hne1 : h+1 ≠ h := by omega
  have hne2 : h+2 ≠ h := by omega
  have hne3 : h+2 ≠ h+1 := by omega
  have hne1' : h ≠ h+1 := by omega
  have hne2' : h ≠ h+2 := by omega
  have hne3' : h+1 ≠ h+2 := by omega
  simp [run, rawStep, readSlot, applyMove, h0, h1, h2,
    hne1, hne2, hne3, hne1', hne2', hne3', valuationSetup3Tape]
  constructor
  · omega
  · funext y
    by_cases hy0 : y = h
    · simp_all [valuationSetup3Tape]
    · by_cases hy1 : y = h+1
      · simp_all [valuationSetup3Tape]
      · by_cases hy2 : y = h+2
        · simp_all [valuationSetup3Tape]
        · simp_all [valuationSetup3Tape]

/-- The seven fixed transitions from state 1 at x to state 5 at x+1. -/
theorem valuation_state1_to_state5 (T : Int → Bool) (x : Int)
    (h0 : T x = false)
    (h1 : T (x-1) = true)
    (h2 : T (x-2) = false)
    (h3 : T (x-3) = false) :
    run tm2 7 ⟨1,x,T⟩ =
      some ⟨5,x+1,valuationSetupTape T x⟩ := by
  have hExit := valuation_state1_exit4 T x h0 h1 h2 h3
  have hx20 : x-2 ≠ x := by omega
  have hx21 : x-2 ≠ x-1 := by omega
  have hx10 : x-1 ≠ x := by omega
  have hx12 : x-1 ≠ x-2 := by omega
  have hx01 : x ≠ x-1 := by omega
  have hx02 : x ≠ x-2 := by omega
  have hx03 : x ≠ x-3 := by omega
  have h0' : valuationExit4Tape T x (x-2) = false := by
    simp [valuationExit4Tape, hx20, hx21]
  have h1' : valuationExit4Tape T x (x-1) = false := by
    simp [valuationExit4Tape, hx10, hx12]
  have h2' : valuationExit4Tape T x x = true := by
    simp [valuationExit4Tape, hx01, hx02, hx03]
  have hcoord1 : (x-2)+1 = x-1 := by omega
  have hcoord2 : (x-2)+2 = x := by omega
  have h1'' : valuationExit4Tape T x ((x-2)+1) = false := by
    simpa [hcoord1] using h1'
  have h2'' : valuationExit4Tape T x ((x-2)+2) = true := by
    simpa [hcoord2] using h2'
  have hSetup := valuation_state4_setup3
    (valuationExit4Tape T x) (x-2) h0' h1'' h2''
  have hTape :
      valuationSetup3Tape (valuationExit4Tape T x) (x-2) =
        valuationSetupTape T x := by
    funext y
    by_cases hy0 : y = x
    · simp_all [valuationSetup3Tape, valuationExit4Tape, valuationSetupTape]
    · by_cases hy1 : y = x-1
      · simp_all [valuationSetup3Tape, valuationExit4Tape, valuationSetupTape]
      · by_cases hy2 : y = x-2
        · simp_all [valuationSetup3Tape, valuationExit4Tape, valuationSetupTape]
        · by_cases hy3 : y = x-3
          · simp_all [valuationSetup3Tape, valuationExit4Tape, valuationSetupTape]
          · simp_all [valuationSetup3Tape, valuationExit4Tape, valuationSetupTape]
  have hnum : 7 = 4+3 := by omega
  rw [hnum, run_append, hExit]
  simp only [Option.bind_some]
  rw [hTape] at hSetup
  have hhead : x-2+3 = x+1 := by omega
  simpa [hhead] using hSetup

theorem valuation_state5_exit1 (T : Int → Bool) (h : Int)
    (h0 : T h = false) :
    run tm2 1 ⟨5,h,T⟩ =
      some ⟨4,h+1,valuationExit1Tape T h⟩ := by
  simp [run, rawStep, readSlot, applyMove, h0]
  funext y
  by_cases hy : y = h <;> simp_all [valuationExit1Tape]

/-- A state-1 sweep leaves its final head blank. -/
theorem state1SweptLeft_head (n : Nat) (T : Int → Bool) (h : Int)
    (h0 : T h = false) :
    state1SweptLeft n T h (h-(n:Int)) = false := by
  induction n generalizing T h with
  | zero =>
      simpa [state1SweptLeft] using h0
  | succ n ih =>
      have hne : h-1 ≠ h := by omega
      have h0' : holeLeft T h (h-1) = false := by
        simp [holeLeft, hne]
      have htail := ih (holeLeft T h) (h-1) h0'
      have hcoord : (h-1)-(n:Int) = h-((n+1:Int)) := by omega
      simpa [state1SweptLeft, hcoord] using htail

/-- The state-1 sweep leaves every cell strictly right of its initial
head unchanged. -/
theorem state1SweptLeft_preserves_right (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : h < x) :
    state1SweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [state1SweptLeft]
  | succ n ih =>
      have hpres := ih (holeLeft T h) (h-1) (by omega)
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h-1 := by omega
      simpa [state1SweptLeft, holeLeft, hne0, hne1] using hpres

/-- The state-1 sweep writes one at every cell strictly right of its
final blank and at or left of its initial head. -/
theorem state1SweptLeft_block (n : Nat) (T : Int → Bool) (h : Int)
    (i : Nat) (hi : i < n) :
    state1SweptLeft n T h (h-(n:Int)+1+(i:Int)) = true := by
  induction n generalizing T h i with
  | zero =>
      omega
  | succ n ih =>
      by_cases hieq : i = n
      · subst i
        have hpres := state1SweptLeft_preserves_right
          n (holeLeft T h) (h-1) h (by omega)
        have hcoord : h-(n+1:Int)+1+(n:Int) = h := by omega
        simpa [state1SweptLeft, hcoord, holeLeft] using hpres
      · have hi' : i < n := by omega
        have htail := ih (holeLeft T h) (h-1) i hi'
        have hcoord :
            (h-1)-(n:Int)+1+(i:Int) =
              h-((n+1:Int))+1+(i:Int) := by omega
        simpa [state1SweptLeft, hcoord] using htail

/-- The state-1 sweep leaves every cell strictly left of its final head
unchanged. -/
theorem state1SweptLeft_preserves_left (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h-(n:Int)) :
    state1SweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [state1SweptLeft]
  | succ n ih =>
      have hx' : x < (h-1)-(n:Int) := by omega
      have hpres := ih (holeLeft T h) (h-1) hx'
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h-1 := by omega
      simpa [state1SweptLeft, holeLeft, hne0, hne1] using hpres

/-- The state-5 sweep leaves every cell strictly left of its initial
head unchanged. -/
theorem state5SweptRight_preserves_left (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h) :
    state5SweptRight n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [state5SweptRight]
  | succ n ih =>
      have hpres := ih (holeRight T h) (h+3) (by omega)
      have hne0 : x ≠ h := by omega
      have hne2 : x ≠ h+2 := by omega
      simpa [state5SweptRight, holeRight, hne0, hne2] using hpres

/-- On a block of 3*n ones, the state-5 right sweep leaves the middle
cell of each triple one and clears the other two. -/
theorem state5SweptRight_block_pattern (n : Nat) (T : Int → Bool)
    (h : Int) (j : Nat) (hj : j < 3*n)
    (hon : state5RightOnes T h (3*n)) :
    state5SweptRight n T h (h+(j:Int)) = decide (j%3 = 1) := by
  induction n generalizing T h j with
  | zero => omega
  | succ n ih =>
      by_cases hj0 : j = 0
      · subst j
        have hpres := state5SweptRight_preserves_left
          n (holeRight T h) (h+3) h (by omega)
        simpa [state5SweptRight, holeRight] using hpres
      · by_cases hj1 : j = 1
        · subst j
          have hpres := state5SweptRight_preserves_left
            n (holeRight T h) (h+3) (h+1) (by omega)
          have hbit := hon 1 (by omega)
          have hbit' : T (h+1) = true := by simpa using hbit
          have hne0 : h+1 ≠ h := by omega
          have hne2 : h+1 ≠ h+2 := by omega
          simpa [state5SweptRight, holeRight, hne0, hne2, hbit'] using hpres
        · by_cases hj2 : j = 2
          · subst j
            have hpres := state5SweptRight_preserves_left
              n (holeRight T h) (h+3) (h+2) (by omega)
            simpa [state5SweptRight, holeRight] using hpres
          · have hj3 : 3 ≤ j := by omega
            have htailOnes :
                state5RightOnes (holeRight T h) (h+3) (3*n) :=
              state5RightOnes_tail T h (3*n) (by
                simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using hon)
            have htail := ih (holeRight T h) (h+3) (j-3) (by omega) htailOnes
            have hcoord : h+3+((j-3:Nat):Int) = h+(j:Int) := by omega
            have hmod : (j-3)%3 = j%3 := by omega
            simp only [state5SweptRight]
            rw [← hcoord, htail, hmod]

/-- The state-1-to-state-4 bridge tape after both sweeps and the final
one-step exit. -/
def m1EvenValuationBridgeTape (v : Nat) (T : Int → Bool) (h : Int) :
    Int → Bool :=
  let N := 3*(v+1)
  let Tleft := state1SweptLeft N T h
  let x := h-(N:Int)
  let Tsetup := valuationSetupTape Tleft x
  let Tright := state5SweptRight (v+1) Tsetup (x+1)
  valuationExit1Tape Tright (h+1)

/-- Beyond the state-5 sweep's right endpoint, the bridge leaves
the state-1 input tape unchanged. -/
theorem m1EvenValuationBridgeTape_preserves_right
    (v : Nat) (T : Int → Bool) (h x : Int)
    (hx : h+2 ≤ x) :
    m1EvenValuationBridgeTape v T h x = T x := by
  let N : Nat := 3*(v+1)
  let x0 : Int := h-(N:Int)
  let Tleft : Int → Bool := state1SweptLeft N T h
  let Tsetup : Int → Bool := valuationSetupTape Tleft x0
  let Tright : Int → Bool := state5SweptRight (v+1) Tsetup (x0+1)
  have hleft : Tleft x = T x := by
    dsimp [Tleft]
    exact state1SweptLeft_preserves_right N T h x (by omega)
  have hneq0 : x ≠ x0 := by dsimp [x0,N]; omega
  have hneq1 : x ≠ x0-1 := by dsimp [x0,N]; omega
  have hneq2 : x ≠ x0-2 := by dsimp [x0,N]; omega
  have hneq3 : x ≠ x0-3 := by dsimp [x0,N]; omega
  have hsetup : Tsetup x = Tleft x := by
    simp [Tsetup, valuationSetupTape, hneq0, hneq1, hneq2, hneq3]
  have hend : x0+1+(3*(v+1):Int) = h+1 := by
    dsimp [x0,N]
    omega
  have hrightBound : x0+1+(3*(v+1:Int)) ≤ x := by
    have hend' : x0+1+(3*(v+1:Int)) = h+1 := by
      dsimp [x0,N] at hend ⊢
      omega
    omega
  have hright : Tright x = Tsetup x := by
    dsimp [Tright]
    exact state5SweptRight_preserves_far_right (v+1) Tsetup (x0+1) x hrightBound
  have hexit : valuationExit1Tape Tright (h+1) x = Tright x := by
    simp [valuationExit1Tape]
    omega
  change valuationExit1Tape Tright (h+1) x = T x
  rw [hexit, hright, hsetup, hleft]

/-- The exact state-1-to-state-4 valuation bridge, for every v≥0. -/
theorem m1EvenValuationBridge_run (v : Nat) (T : Int → Bool) (h : Int)
    (h0 : T h = false)
    (hon : state1LeftOnes T h (3*(v+1)+1))
    (hz1 : T (h-((3*(v+1)+2 : Nat):Int)) = false)
    (hz2 : T (h-((3*(v+1)+3 : Nat):Int)) = false)
    (hr1 : T (h+1) = false)
    (hr2 : T (h+2) = true)
    (hr3 : T (h+3) = true)
    (hr4 : T (h+4) = true) :
    run tm2 (12*v+23) ⟨1,h,T⟩ =
      some ⟨4,h+5,m1EvenValuationBridgeTape v T h⟩ := by
  let N : Nat := 3*(v+1)
  let x : Int := h-(N:Int)
  let Tleft : Int → Bool := state1SweptLeft N T h
  let Tsetup : Int → Bool := valuationSetupTape Tleft x
  let Tright : Int → Bool := state5SweptRight (v+1) Tsetup (x+1)
  let Tout : Int → Bool := valuationExit1Tape Tright (h+1)
  have hleftHead : Tleft x = false := by
    dsimp [Tleft,x,N]
    exact state1SweptLeft_head N T h h0
  have hleftExtra : Tleft (x-1) = true := by
    have hpres := state1SweptLeft_preserves_left N T h (x-1) (by
      dsimp [x,N]
      omega)
    change state1SweptLeft N T h (x-1) = true
    rw [hpres]
    have hbit := hon N (by dsimp [N]; omega)
    have hcoord : h-1-(N:Int) = x-1 := by dsimp [x]; omega
    rw [← hcoord]
    exact hbit
  have hleftZero1 : Tleft (x-2) = false := by
    have hpres := state1SweptLeft_preserves_left N T h (x-2) (by
      dsimp [x,N]
      omega)
    change state1SweptLeft N T h (x-2) = false
    rw [hpres]
    have hcoord : x-2 = h-((3*(v+1)+2:Nat):Int) := by
      dsimp [x,N]
      omega
    rw [hcoord]
    exact hz1
  have hleftZero2 : Tleft (x-3) = false := by
    have hpres := state1SweptLeft_preserves_left N T h (x-3) (by
      dsimp [x,N]
      omega)
    change state1SweptLeft N T h (x-3) = false
    rw [hpres]
    have hcoord : x-3 = h-((3*(v+1)+3:Nat):Int) := by
      dsimp [x,N]
      omega
    rw [hcoord]
    exact hz2
  have hsetupRun := valuation_state1_to_state5
    Tleft x hleftHead hleftExtra hleftZero1 hleftZero2
  have hsetupEq : valuationSetupTape Tleft x = Tsetup := by rfl
  rw [hsetupEq] at hsetupRun
  have hrightOnes : state5RightOnes Tsetup (x+1) (3*(v+1)) := by
    intro i hi
    have hblock := state1SweptLeft_block N T h i (by
      dsimp [N]
      omega)
    have hcoord : (x+1)+(i:Int) = h-(N:Int)+1+(i:Int) := by
      dsimp [x]
    have hsetupCell : Tsetup ((x+1)+(i:Int)) =
        Tleft ((x+1)+(i:Int)) := by
      have hne0 : (x+1)+(i:Int) ≠ x := by omega
      have hne1 : (x+1)+(i:Int) ≠ x-1 := by omega
      have hne2 : (x+1)+(i:Int) ≠ x-2 := by omega
      have hne3 : (x+1)+(i:Int) ≠ x-3 := by omega
      simp [Tsetup, valuationSetupTape, hne0, hne1, hne2, hne3]
    rw [hsetupCell, hcoord]
    simpa [Tleft] using hblock
  have hrightRun := counted_right_sweep_from5 (v+1) Tsetup (x+1) hrightOnes
  have hrightEnd : x+1+(3*(v+1):Int) = h+1 := by
    dsimp [x,N]
    omega
  have hrightEnd' : x+1+3*(↑(v+1)) = h+1 := by omega
  rw [hrightEnd'] at hrightRun
  have hfar1 : Tright (h+1) = Tsetup (h+1) := by
    dsimp [Tright]
    rw [state5SweptRight_preserves_far_right (v+1) Tsetup (x+1)
      (h+1) (by rw [hrightEnd']; omega)]
  have hleftRight1 : Tleft (h+1) = T (h+1) := by
    dsimp [Tleft]
    exact state1SweptLeft_preserves_right N T h (h+1) (by omega)
  have hleftRight2 : Tleft (h+2) = T (h+2) := by
    dsimp [Tleft]
    exact state1SweptLeft_preserves_right N T h (h+2) (by omega)
  have hleftRight3 : Tleft (h+3) = T (h+3) := by
    dsimp [Tleft]
    exact state1SweptLeft_preserves_right N T h (h+3) (by omega)
  have hleftRight4 : Tleft (h+4) = T (h+4) := by
    dsimp [Tleft]
    exact state1SweptLeft_preserves_right N T h (h+4) (by omega)
  have hsetupRight1 : Tsetup (h+1) = false := by
    have hne0 : h+1 ≠ x := by dsimp [x,N]; omega
    have hne1 : h+1 ≠ x-1 := by dsimp [x,N]; omega
    have hne2 : h+1 ≠ x-2 := by dsimp [x,N]; omega
    have hne3 : h+1 ≠ x-3 := by dsimp [x,N]; omega
    simp [Tsetup, valuationSetupTape, hne0, hne1, hne2, hne3]
    rw [hleftRight1]
    exact hr1
  have hfar2 : Tright (h+2) = Tsetup (h+2) := by
    dsimp [Tright]
    rw [state5SweptRight_preserves_far_right (v+1) Tsetup (x+1)
      (h+2) (by rw [hrightEnd']; omega)]
  have hsetupRight2 : Tsetup (h+2) = true := by
    have hne0 : h+2 ≠ x := by dsimp [x,N]; omega
    have hne1 : h+2 ≠ x-1 := by dsimp [x,N]; omega
    have hne2 : h+2 ≠ x-2 := by dsimp [x,N]; omega
    have hne3 : h+2 ≠ x-3 := by dsimp [x,N]; omega
    simp [Tsetup, valuationSetupTape, hne0, hne1, hne2, hne3]
    rw [hleftRight2]
    exact hr2
  have hfar3 : Tright (h+3) = Tsetup (h+3) := by
    dsimp [Tright]
    rw [state5SweptRight_preserves_far_right (v+1) Tsetup (x+1)
      (h+3) (by rw [hrightEnd']; omega)]
  have hsetupRight3 : Tsetup (h+3) = true := by
    have hne0 : h+3 ≠ x := by dsimp [x,N]; omega
    have hne1 : h+3 ≠ x-1 := by dsimp [x,N]; omega
    have hne2 : h+3 ≠ x-2 := by dsimp [x,N]; omega
    have hne3 : h+3 ≠ x-3 := by dsimp [x,N]; omega
    simp [Tsetup, valuationSetupTape, hne0, hne1, hne2, hne3]
    rw [hleftRight3]
    exact hr3
  have hfar4 : Tright (h+4) = Tsetup (h+4) := by
    dsimp [Tright]
    rw [state5SweptRight_preserves_far_right (v+1) Tsetup (x+1)
      (h+4) (by rw [hrightEnd']; omega)]
  have hsetupRight4 : Tsetup (h+4) = true := by
    have hne0 : h+4 ≠ x := by dsimp [x,N]; omega
    have hne1 : h+4 ≠ x-1 := by dsimp [x,N]; omega
    have hne2 : h+4 ≠ x-2 := by dsimp [x,N]; omega
    have hne3 : h+4 ≠ x-3 := by dsimp [x,N]; omega
    simp [Tsetup, valuationSetupTape, hne0, hne1, hne2, hne3]
    rw [hleftRight4]
    exact hr4
  have hblank : Tright (h+1) = false := by rw [hfar1,hsetupRight1]
  have hExit := valuation_state5_exit1 Tright (h+1) hblank
  have hlinear : linearRightOnes (valuationExit1Tape Tright (h+1))
      (h+2) 3 := by
    intro i hi
    have hiCases : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hiCases with hi0 | hi1 | hi2
    · subst i
      simpa [valuationExit1Tape] using hfar2.trans hsetupRight2
    · subst i
      have hcoord : h+2+1 = h+3 := by omega
      have hne : h+2+1 ≠ h+1 := by omega
      simpa [valuationExit1Tape, hne, hcoord] using hfar3.trans hsetupRight3
    · subst i
      have hcoord : h+2+2 = h+4 := by omega
      have hne : h+2+2 ≠ h+1 := by omega
      simpa [valuationExit1Tape, hne, hcoord] using hfar4.trans hsetupRight4
  have hscan := E_scan (valuationExit1Tape Tright (h+1)) (h+2) 3 hlinear
  have hleftRun := counted_left_sweep_from1 N T h h0 hon
  have hnum1 : 12*v+23 = 3*N + (7 + (3*(v+1) + (1+3))) := by
    dsimp [N]
    omega
  rw [hnum1, run_append, hleftRun]
  simp only [Option.bind_some]
  rw [run_append, hsetupRun]
  simp only [Option.bind_some]
  rw [run_append, hrightRun]
  simp only [Option.bind_some]
  rw [run_append, hExit]
  simp only [Option.bind_some]
  have hhead : h+2+3 = h+5 := by omega
  simpa [m1EvenValuationBridgeTape, N, x, Tleft, Tsetup, Tright, Tout, hhead] using hscan

#print axioms valuation_state1_exit4
#print axioms valuation_state4_setup3
#print axioms valuation_state1_to_state5
#print axioms state1SweptLeft_head
#print axioms state1SweptLeft_block
#print axioms state1SweptLeft_preserves_left
#print axioms state5SweptRight_preserves_left
#print axioms state5SweptRight_block_pattern
#print axioms m1EvenValuationBridge_run

end BB6Coverage.Agent48M1EvenValuationBridge
