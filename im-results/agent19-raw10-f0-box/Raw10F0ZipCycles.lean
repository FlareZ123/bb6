import Raw10FixedLeaves
import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19Raw10F0Box

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent10ZipAudit

/-- Decode the repository's integer transition code
    1 + 4*next + 2*write + right into a local Move. -/
def moveOfCode (c : Fin 25) : Move :=
  let n := c.val - 1
  { write := decide (n / 2 % 2 = 1)
    right := decide (n % 2 = 1)
    next := ⟨n / 4, by have hc := c.isLt; omega⟩ }

/-- A fixed code of zero means a halt transition; nonzero codes are ordinary moves. -/
def entryOfCode (c : Fin 25) : Option Transition :=
  if c.val = 0 then some none else some (some (moveOfCode c))

/-- The first ten transitions of the 575-completion residual box. -/
def raw10Prefix : PartialMachine := fun s =>
  if s = (0, false) then some (some ⟨true, true, 1⟩)
  else if s = (0, true) then some (some ⟨false, true, 3⟩)
  else if s = (1, false) then some (some ⟨true, false, 2⟩)
  else if s = (1, true) then some (some ⟨true, false, 1⟩)
  else if s = (2, false) then some (some ⟨false, false, 4⟩)
  else if s = (2, true) then some (some ⟨true, true, 0⟩)
  else if s = (3, false) then some (some ⟨false, false, 2⟩)
  else if s = (3, true) then some (some ⟨false, true, 0⟩)
  else if s = (4, false) then some (some ⟨true, true, 5⟩)
  else if s = (4, true) then some (some ⟨true, false, 3⟩)
  else none

/-- Fix F0 while leaving F1 open. -/
def raw10WithF0 (f0 : Fin 25) : PartialMachine := fun s =>
  if s = (5, false) then entryOfCode f0 else raw10Prefix s

/-- Fix both F0 and F1. -/
def raw10WithF0F1 (f0 f1 : Fin 25) : PartialMachine := fun s =>
  if s = (5, false) then entryOfCode f0
  else if s = (5, true) then entryOfCode f1
  else raw10Prefix s

theorem f0Zip_sound (f0 : Fin 25) (entry period : Nat)
    (right : Bool) (boundary : Int) (hn : 0 < period)
    (hzip : zipCycle (raw10WithF0 f0) entry period right boundary = true) :
    ∀ m, compatible (raw10WithF0 f0) m → NeverHalts m :=
  zipCycle_sound (raw10WithF0 f0) entry period right boundary hn hzip

theorem f0f1Zip_sound (f0 f1 : Fin 25) (entry period : Nat)
    (right : Bool) (boundary : Int) (hn : 0 < period)
    (hzip : zipCycle (raw10WithF0F1 f0 f1) entry period right boundary = true) :
    ∀ m, compatible (raw10WithF0F1 f0 f1) m → NeverHalts m :=
  zipCycle_sound (raw10WithF0F1 f0 f1) entry period right boundary hn hzip

/-- Seventeen F0 values yield one-sided zipper cycles with F1 entirely free. -/
theorem f0_2_never :
    ∀ m, compatible (raw10WithF0 (⟨2, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨2, by decide⟩ : Fin 25) 10 5 false (-2 : Int) (by decide) (by decide)

theorem f0_3_never :
    ∀ m, compatible (raw10WithF0 (⟨3, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨3, by decide⟩ : Fin 25) 10 7 false (-4 : Int) (by decide) (by decide)

theorem f0_4_never :
    ∀ m, compatible (raw10WithF0 (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨4, by decide⟩ : Fin 25) 10 8 false (-2 : Int) (by decide) (by decide)

theorem f0_5_never :
    ∀ m, compatible (raw10WithF0 (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨5, by decide⟩ : Fin 25) 10 4 false (-4 : Int) (by decide) (by decide)

theorem f0_6_never :
    ∀ m, compatible (raw10WithF0 (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨6, by decide⟩ : Fin 25) 10 5 false (-3 : Int) (by decide) (by decide)

theorem f0_7_never :
    ∀ m, compatible (raw10WithF0 (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨7, by decide⟩ : Fin 25) 10 4 false (-4 : Int) (by decide) (by decide)

theorem f0_8_never :
    ∀ m, compatible (raw10WithF0 (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨8, by decide⟩ : Fin 25) 10 6 false (-3 : Int) (by decide) (by decide)

theorem f0_9_never :
    ∀ m, compatible (raw10WithF0 (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨9, by decide⟩ : Fin 25) 10 3 false (-4 : Int) (by decide) (by decide)

theorem f0_11_never :
    ∀ m, compatible (raw10WithF0 (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨11, by decide⟩ : Fin 25) 10 3 false (-4 : Int) (by decide) (by decide)

theorem f0_13_never :
    ∀ m, compatible (raw10WithF0 (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨13, by decide⟩ : Fin 25) 10 4 false (-4 : Int) (by decide) (by decide)

theorem f0_15_never :
    ∀ m, compatible (raw10WithF0 (⟨15, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨15, by decide⟩ : Fin 25) 10 4 false (-4 : Int) (by decide) (by decide)

theorem f0_17_never :
    ∀ m, compatible (raw10WithF0 (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨17, by decide⟩ : Fin 25) 10 2 false (-4 : Int) (by decide) (by decide)

theorem f0_18_never :
    ∀ m, compatible (raw10WithF0 (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨18, by decide⟩ : Fin 25) 10 5 false (-3 : Int) (by decide) (by decide)

theorem f0_19_never :
    ∀ m, compatible (raw10WithF0 (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨19, by decide⟩ : Fin 25) 10 2 false (-4 : Int) (by decide) (by decide)

theorem f0_20_never :
    ∀ m, compatible (raw10WithF0 (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨20, by decide⟩ : Fin 25) 10 7 false (-2 : Int) (by decide) (by decide)

theorem f0_21_never :
    ∀ m, compatible (raw10WithF0 (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨21, by decide⟩ : Fin 25) 10 1 false (-4 : Int) (by decide) (by decide)

theorem f0_23_never :
    ∀ m, compatible (raw10WithF0 (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0Zip_sound (⟨23, by decide⟩ : Fin 25) 10 1 false (-4 : Int) (by decide) (by decide)

/-- Sixty-five early-F1 singleton completions yield zipper cycles. -/
theorem f0f1_12_2_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨2, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨2, by decide⟩ : Fin 25) 24 19 false (0 : Int) (by decide) (by decide)

theorem f0f1_12_3_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨3, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨3, by decide⟩ : Fin 25) 34 10 false (-4 : Int) (by decide) (by decide)

theorem f0f1_12_4_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25) 10 30 false (3 : Int) (by decide) (by decide)

theorem f0f1_12_5_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25) 33 10 false (-5 : Int) (by decide) (by decide)

theorem f0f1_12_6_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25) 33 10 false (-3 : Int) (by decide) (by decide)

theorem f0f1_12_7_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25) 33 10 false (-5 : Int) (by decide) (by decide)

theorem f0f1_12_8_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25) 33 10 false (-3 : Int) (by decide) (by decide)

theorem f0f1_12_9_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25) 10 25 false (3 : Int) (by decide) (by decide)

theorem f0f1_12_10_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25) 24 28 true (-10 : Int) (by decide) (by decide)

theorem f0f1_12_11_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25) 33 10 false (-4 : Int) (by decide) (by decide)

theorem f0f1_12_12_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25) 24 14 true (-10 : Int) (by decide) (by decide)

theorem f0f1_12_13_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25) 24 18 false (0 : Int) (by decide) (by decide)

theorem f0f1_12_16_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25) 44 10 false (-2 : Int) (by decide) (by decide)

theorem f0f1_12_17_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25) 33 10 false (-3 : Int) (by decide) (by decide)

theorem f0f1_12_18_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25) 10 27 false (3 : Int) (by decide) (by decide)

theorem f0f1_12_19_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25) 24 35 false (0 : Int) (by decide) (by decide)

theorem f0f1_12_20_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25) 24 21 false (0 : Int) (by decide) (by decide)

theorem f0f1_12_21_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25) 25 25 false (-1 : Int) (by decide) (by decide)

theorem f0f1_12_23_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25) 24 26 false (0 : Int) (by decide) (by decide)

theorem f0f1_12_24_never :
    ∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨12, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25) 25 10 true (-11 : Int) (by decide) (by decide)

theorem f0f1_22_1_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨1, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨1, by decide⟩ : Fin 25) 10 12 false (-2 : Int) (by decide) (by decide)

theorem f0f1_22_3_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨3, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨3, by decide⟩ : Fin 25) 10 8 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_4_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25) 24 14 true (-10 : Int) (by decide) (by decide)

theorem f0f1_22_5_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25) 10 5 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_6_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25) 10 5 false (-2 : Int) (by decide) (by decide)

theorem f0f1_22_7_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25) 10 5 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_8_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25) 10 11 false (-1 : Int) (by decide) (by decide)

theorem f0f1_22_9_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25) 10 4 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_10_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25) 10 4 true (-14 : Int) (by decide) (by decide)

theorem f0f1_22_11_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25) 10 4 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_12_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25) 10 7 false (-2 : Int) (by decide) (by decide)

theorem f0f1_22_13_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25) 10 5 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_14_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨14, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨14, by decide⟩ : Fin 25) 10 5 false (-2 : Int) (by decide) (by decide)

theorem f0f1_22_15_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨15, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨15, by decide⟩ : Fin 25) 10 5 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_16_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25) 26 16 true (-10 : Int) (by decide) (by decide)

theorem f0f1_22_17_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25) 10 3 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_18_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25) 10 12 true (-14 : Int) (by decide) (by decide)

theorem f0f1_22_19_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25) 10 3 false (-3 : Int) (by decide) (by decide)

theorem f0f1_22_20_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25) 10 10 true (-14 : Int) (by decide) (by decide)

theorem f0f1_22_21_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25) 17 1 true (-11 : Int) (by decide) (by decide)

theorem f0f1_22_22_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨22, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨22, by decide⟩ : Fin 25) 15 1 true (-9 : Int) (by decide) (by decide)

theorem f0f1_22_23_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25) 10 2 true (-14 : Int) (by decide) (by decide)

theorem f0f1_22_24_never :
    ∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨22, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25) 15 1 true (1 : Int) (by decide) (by decide)

theorem f0f1_24_1_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨1, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨1, by decide⟩ : Fin 25) 10 6 false (-3 : Int) (by decide) (by decide)

theorem f0f1_24_4_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25) 10 30 false (3 : Int) (by decide) (by decide)

theorem f0f1_24_5_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25) 10 6 false (-3 : Int) (by decide) (by decide)

theorem f0f1_24_6_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25) 10 8 false (-2 : Int) (by decide) (by decide)

theorem f0f1_24_7_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25) 10 6 false (-3 : Int) (by decide) (by decide)

theorem f0f1_24_8_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25) 10 13 false (-1 : Int) (by decide) (by decide)

theorem f0f1_24_9_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25) 10 15 false (-1 : Int) (by decide) (by decide)

theorem f0f1_24_10_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25) 28 18 true (-10 : Int) (by decide) (by decide)

theorem f0f1_24_11_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25) 10 10 false (-2 : Int) (by decide) (by decide)

theorem f0f1_24_12_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25) 10 9 false (-2 : Int) (by decide) (by decide)

theorem f0f1_24_13_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25) 10 13 false (-1 : Int) (by decide) (by decide)

theorem f0f1_24_14_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨14, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨14, by decide⟩ : Fin 25) 10 8 false (-2 : Int) (by decide) (by decide)

theorem f0f1_24_15_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨15, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨15, by decide⟩ : Fin 25) 10 7 false (-2 : Int) (by decide) (by decide)

theorem f0f1_24_16_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25) 46 12 false (-2 : Int) (by decide) (by decide)

theorem f0f1_24_17_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25) 10 6 false (-3 : Int) (by decide) (by decide)

theorem f0f1_24_18_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25) 23 16 false (-1 : Int) (by decide) (by decide)

theorem f0f1_24_19_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25) 10 6 false (-3 : Int) (by decide) (by decide)

theorem f0f1_24_20_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25) 10 17 false (-1 : Int) (by decide) (by decide)

theorem f0f1_24_21_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25) 24 1 true (-6 : Int) (by decide) (by decide)

theorem f0f1_24_22_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨22, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨22, by decide⟩ : Fin 25) 15 1 true (1 : Int) (by decide) (by decide)

theorem f0f1_24_23_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25) 10 3 false (-3 : Int) (by decide) (by decide)

theorem f0f1_24_24_never :
    ∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25)) m → NeverHalts m :=
  f0f1Zip_sound (⟨24, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25) 15 1 true (-4 : Int) (by decide) (by decide)

/-- Aggregate axiom-audit targets for the two proved nonhalting families. -/
theorem raw10F0ZipLeaves :
    (∀ m, compatible (raw10WithF0 (⟨2, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨3, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨15, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0 (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m) := by
  exact ⟨f0_2_never,
    f0_3_never,
    f0_4_never,
    f0_5_never,
    f0_6_never,
    f0_7_never,
    f0_8_never,
    f0_9_never,
    f0_11_never,
    f0_13_never,
    f0_15_never,
    f0_17_never,
    f0_18_never,
    f0_19_never,
    f0_20_never,
    f0_21_never,
    f0_23_never⟩

theorem raw10F0F1ZipLeaves :
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨2, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨3, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨1, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨3, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨14, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨15, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨22, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨1, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨4, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨5, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨6, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨7, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨8, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨9, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨10, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨11, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨12, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨13, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨14, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨15, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨16, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨17, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨18, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨19, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨20, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨21, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨22, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨23, by decide⟩ : Fin 25)) m → NeverHalts m) ∧
    (∀ m, compatible (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨24, by decide⟩ : Fin 25)) m → NeverHalts m) := by
  exact ⟨f0f1_12_2_never,
    f0f1_12_3_never,
    f0f1_12_4_never,
    f0f1_12_5_never,
    f0f1_12_6_never,
    f0f1_12_7_never,
    f0f1_12_8_never,
    f0f1_12_9_never,
    f0f1_12_10_never,
    f0f1_12_11_never,
    f0f1_12_12_never,
    f0f1_12_13_never,
    f0f1_12_16_never,
    f0f1_12_17_never,
    f0f1_12_18_never,
    f0f1_12_19_never,
    f0f1_12_20_never,
    f0f1_12_21_never,
    f0f1_12_23_never,
    f0f1_12_24_never,
    f0f1_22_1_never,
    f0f1_22_3_never,
    f0f1_22_4_never,
    f0f1_22_5_never,
    f0f1_22_6_never,
    f0f1_22_7_never,
    f0f1_22_8_never,
    f0f1_22_9_never,
    f0f1_22_10_never,
    f0f1_22_11_never,
    f0f1_22_12_never,
    f0f1_22_13_never,
    f0f1_22_14_never,
    f0f1_22_15_never,
    f0f1_22_16_never,
    f0f1_22_17_never,
    f0f1_22_18_never,
    f0f1_22_19_never,
    f0f1_22_20_never,
    f0f1_22_21_never,
    f0f1_22_22_never,
    f0f1_22_23_never,
    f0f1_22_24_never,
    f0f1_24_1_never,
    f0f1_24_4_never,
    f0f1_24_5_never,
    f0f1_24_6_never,
    f0f1_24_7_never,
    f0f1_24_8_never,
    f0f1_24_9_never,
    f0f1_24_10_never,
    f0f1_24_11_never,
    f0f1_24_12_never,
    f0f1_24_13_never,
    f0f1_24_14_never,
    f0f1_24_15_never,
    f0f1_24_16_never,
    f0f1_24_17_never,
    f0f1_24_18_never,
    f0f1_24_19_never,
    f0f1_24_20_never,
    f0f1_24_21_never,
    f0f1_24_22_never,
    f0f1_24_23_never,
    f0f1_24_24_never⟩


/-- Transfer a finite zipper trace ending at a halting query to every
    compatible total machine. This is the same source-level bridge used by
    Raw10FixedLeaves.halt_exact. -/
theorem haltsAfter_of_zrun_halt (p : PartialMachine) (n : Nat) (entry : Z)
    (hentry : zrun p n start = some entry)
    (hquery : p (entry.q, entry.l.headD false) = some none) :
    ∀ m, compatible p m → HaltsAfter m n := by
  intro m hm
  have hrun := zrun_sound p m hm n entry hentry
  rw [start_embed] at hrun
  have hstep : rawStep m (embed entry) = none := by
    rw [rawStep, read_embed, hm _ _ hquery]
    rfl
  refine ⟨embed entry, hrun, ?_⟩
  rw [run, hrun]
  exact hstep

/-- The first-one delay list is always a filter of range 6. -/
theorem raw10_delay_bound_any (p : PartialMachine) (n : Nat)
    (hn : n + 7 ≤ 6766859) :
    ∀ d ∈ possibleDelays p 0, d + n + 1 ≤ 6766859 := by
  intro d hd
  have hmem : d ∈ List.range 6 := (List.mem_filter.mp hd).1
  have hlt : d < 6 := List.mem_range.mp hmem
  omega

def haltEntryF0 : Z := ⟨5, -4, [], [true, false, false, true, false, false]⟩

theorem haltEntryF0_reached :
    zrun (raw10WithF0 (⟨0, by decide⟩ : Fin 25)) 10 start =
      some haltEntryF0 := by decide

theorem haltEntryF0_query :
    raw10WithF0 (⟨0, by decide⟩ : Fin 25)
      (haltEntryF0.q, haltEntryF0.l.headD false) = some none := by decide

theorem f0_halts_after_10 :
    ∀ m, compatible (raw10WithF0 (⟨0, by decide⟩ : Fin 25)) m →
      HaltsAfter m 10 :=
  haltsAfter_of_zrun_halt (raw10WithF0 (⟨0, by decide⟩ : Fin 25))
    10 haltEntryF0 haltEntryF0_reached haltEntryF0_query

theorem f0_halt_cover :
    Cover (WeightedBound 6766859) (raw10WithF0 (⟨0, by decide⟩ : Fin 25)) :=
  weighted_halt_leaf (raw10WithF0 (⟨0, by decide⟩ : Fin 25))
    6766859 10 (by decide) f0_halts_after_10
    (raw10_delay_bound_any _ 10 (by decide))

def haltEntry12_0 : Z :=
  ⟨5, -4, [true], [true, false, false, false, true, false, false]⟩

theorem haltEntry12_0_reached :
    zrun (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
      32 start = some haltEntry12_0 := by decide

theorem haltEntry12_0_query :
    raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)
      (haltEntry12_0.q, haltEntry12_0.l.headD false) = some none := by decide

theorem f0f1_12_0_halts_after_32 :
    ∀ m, compatible
      (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) m →
      HaltsAfter m 32 :=
  haltsAfter_of_zrun_halt
    (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
    32 haltEntry12_0 haltEntry12_0_reached haltEntry12_0_query

theorem f0f1_12_0_halt_cover :
    Cover (WeightedBound 6766859)
      (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) :=
  weighted_halt_leaf
    (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
    6766859 32 (by decide) f0f1_12_0_halts_after_32
    (raw10_delay_bound_any _ 32 (by decide))

def haltEntry22_0 : Z :=
  ⟨5, -3, [true, false], [false, false, true, false, false]⟩

theorem haltEntry22_0_reached :
    zrun (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
      11 start = some haltEntry22_0 := by decide

theorem haltEntry22_0_query :
    raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)
      (haltEntry22_0.q, haltEntry22_0.l.headD false) = some none := by decide

theorem f0f1_22_0_halts_after_11 :
    ∀ m, compatible
      (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) m →
      HaltsAfter m 11 :=
  haltsAfter_of_zrun_halt
    (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
    11 haltEntry22_0 haltEntry22_0_reached haltEntry22_0_query

theorem f0f1_22_0_halt_cover :
    Cover (WeightedBound 6766859)
      (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) :=
  weighted_halt_leaf
    (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
    6766859 11 (by decide) f0f1_22_0_halts_after_11
    (raw10_delay_bound_any _ 11 (by decide))

def haltEntry24_0 : Z :=
  ⟨5, -3, [true, true], [false, false, true, false, false]⟩

theorem haltEntry24_0_reached :
    zrun (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
      11 start = some haltEntry24_0 := by decide

theorem haltEntry24_0_query :
    raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)
      (haltEntry24_0.q, haltEntry24_0.l.headD false) = some none := by decide

theorem f0f1_24_0_halts_after_11 :
    ∀ m, compatible
      (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) m →
      HaltsAfter m 11 :=
  haltsAfter_of_zrun_halt
    (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
    11 haltEntry24_0 haltEntry24_0_reached haltEntry24_0_query

theorem f0f1_24_0_halt_cover :
    Cover (WeightedBound 6766859)
      (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) :=
  weighted_halt_leaf
    (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25))
    6766859 11 (by decide) f0f1_24_0_halts_after_11
    (raw10_delay_bound_any _ 11 (by decide))

theorem raw10HaltCovers :
    Cover (WeightedBound 6766859) (raw10WithF0 (⟨0, by decide⟩ : Fin 25)) ∧
    Cover (WeightedBound 6766859)
      (raw10WithF0F1 (⟨12, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) ∧
    Cover (WeightedBound 6766859)
      (raw10WithF0F1 (⟨22, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) ∧
    Cover (WeightedBound 6766859)
      (raw10WithF0F1 (⟨24, by decide⟩ : Fin 25) (⟨0, by decide⟩ : Fin 25)) :=
  ⟨f0_halt_cover, f0f1_12_0_halt_cover,
    f0f1_22_0_halt_cover, f0f1_24_0_halt_cover⟩

/-- Exact F0 domain of this residual product box: codes 10 and 16 were
    already removed by the preceding side/cycle certificates. -/
def f0Domain : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24]

def f0ZipCodes : List Nat := [2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 18, 19, 20, 21, 23]
def f0HaltCodes : List Nat := [0]
def f0OpenCodes : List Nat := [1, 14]
def f0BranchCodes : List Nat := [12, 22, 24]
def f1Codes : List Nat := List.range 25

def branchZipPairs : List (Nat × Nat) := [(12, 2), (12, 3), (12, 4), (12, 5), (12, 6), (12, 7), (12, 8), (12, 9), (12, 10), (12, 11), (12, 12), (12, 13), (12, 16), (12, 17), (12, 18), (12, 19), (12, 20), (12, 21), (12, 23), (12, 24), (22, 1), (22, 3), (22, 4), (22, 5), (22, 6), (22, 7), (22, 8), (22, 9), (22, 10), (22, 11), (22, 12), (22, 13), (22, 14), (22, 15), (22, 16), (22, 17), (22, 18), (22, 19), (22, 20), (22, 21), (22, 22), (22, 23), (22, 24), (24, 1), (24, 4), (24, 5), (24, 6), (24, 7), (24, 8), (24, 9), (24, 10), (24, 11), (24, 12), (24, 13), (24, 14), (24, 15), (24, 16), (24, 17), (24, 18), (24, 19), (24, 20), (24, 21), (24, 22), (24, 23), (24, 24)]
def branchHaltPairs : List (Nat × Nat) := [(12, 0), (22, 0), (24, 0)]
def branchOpenPairs : List (Nat × Nat) := [(12, 1), (12, 14), (12, 15), (12, 22), (22, 2), (24, 2), (24, 3)]

theorem f0Domain_partition :
    f0Domain.toFinset =
      f0ZipCodes.toFinset ∪ f0HaltCodes.toFinset ∪
        f0OpenCodes.toFinset ∪ f0BranchCodes.toFinset := by
  decide

theorem branchPair_partition :
    branchZipPairs.toFinset ∪ branchHaltPairs.toFinset ∪ branchOpenPairs.toFinset =
      (f0BranchCodes.flatMap fun f0 => f1Codes.map fun f1 => (f0, f1)).toFinset := by
  decide

theorem f0ZipCodes_count : f0ZipCodes.length = 17 := by decide
theorem branchZipPairs_count : branchZipPairs.length = 65 := by decide
theorem branchHaltPairs_count : branchHaltPairs.length = 3 := by decide
theorem branchOpenPairs_count : branchOpenPairs.length = 7 := by decide
theorem raw10Box_total_count : f0Domain.length * 25 = 575 := by decide
theorem raw10NonhaltCount : f0ZipCodes.length * 25 + branchZipPairs.length = 490 := by decide
theorem raw10ObservedHaltCount : f0HaltCodes.length * 25 + branchHaltPairs.length = 28 := by decide
theorem raw10OpenCount : f0OpenCodes.length * 25 + branchOpenPairs.length = 57 := by decide
theorem raw10Partition_count : 490 + 28 + 57 = 575 := by decide

#print axioms raw10F0ZipLeaves
#print axioms raw10F0F1ZipLeaves
#print axioms raw10HaltCovers
#print axioms f0Domain_partition
#print axioms branchPair_partition

end BB6.Agent19Raw10F0Box
