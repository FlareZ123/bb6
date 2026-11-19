import CountedSweep
import CountedRst1Prime
import Lean.Elab.Tactic.Omega

/-!
# Positive-z first q4-cycle: reusable source bridges

This is an intermediate source draft for the first q4 cycle after the
marker-1 checkpoint. It isolates the two short finite bridges and packages
the post-drain Q(z) phase as a counted left sweep plus a four-step bridge.

The 22-step and four-step finite traces are checked by decide when this
module is compiled. The arbitrary-tape lifts use the original TM63 run
semantics. This file has NOT yet passed local Lean 4.36.0-rc2 compilation;
do not treat it as an accepted proof until the exact import closure and
axiom reports are checked.

The q4-specific S0 input hypotheses in firstCycleQ_from_S0Input are the
ones supplied by the candidate prefix endpoint:
  a = 2^z - 1,
  h = 3*2^z + 3*z + 7,
  k = 3*a + 3*z + 7 = h - 3,
  left run = 1^k, right boundary = 0,
  cells 0,1,2,3 = 0,0,1,0.
-/

namespace BB6Coverage.Agent48PositiveZFirstCycle

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime

/-! ## The 22-step q4-checkpoint-1 prefix bridge -/

/-- The finite window read by the first fixed bridge, relative to head 1. -/
def firstCyclePrefix22Inside (x : Int) : Bool :=
  decide (-4 ≤ x ∧ x ≤ 3)

/-- At the q4 checkpoint the bridge sees 00110000 on offsets -4..3. -/
def firstCyclePrefix22Start : FConfig :=
  ⟨4, 0, [-2,-1]⟩

/-- The 22-step bridge ends at state 4, four cells to the right. -/
def firstCyclePrefix22End : FConfig :=
  ⟨4, 4, [-4,-3,-2,1,3]⟩

theorem firstCyclePrefix22_exact :
    fRun tm2 22 firstCyclePrefix22Start =
      some firstCyclePrefix22End := by
  decide

/-- All 22 pre-step head positions lie in the certified eight-cell window. -/
theorem firstCyclePrefix22_heads :
    (List.range 22).all (fun k =>
      match fRun tm2 k firstCyclePrefix22Start with
      | none => true
      | some f => firstCyclePrefix22Inside f.head) = true := by
  decide

/-- Arbitrary-tape lift of the fixed 22-step prefix bridge. -/
theorem firstCyclePrefix22_at (T : Int → Bool) (h : Int)
    (hinput :
      T (h-4) = false ∧
      T (h-3) = false ∧
      T (h-2) = true ∧
      T (h-1) = true ∧
      T h = false ∧
      T (h+1) = false ∧
      T (h+2) = false ∧
      T (h+3) = false) :
    run tm2 22 ⟨4,h,T⟩ =
      some (frameAt T h firstCyclePrefix22Inside firstCyclePrefix22End) := by
  rcases hinput with ⟨h4,h3,h2,h1,h0,hp1,hp2,hp3⟩
  apply bridgeAt T h firstCyclePrefix22Inside
    firstCyclePrefix22Start firstCyclePrefix22End 22 rfl
    firstCyclePrefix22_exact firstCyclePrefix22_heads
  intro x hx
  have hrange : -4 ≤ x ∧ x ≤ 3 := by
    simpa [firstCyclePrefix22Inside] using hx
  have hcases :
      x=(-4) ∨ x=(-3) ∨ x=(-2) ∨ x=(-1) ∨
      x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega
  rcases hcases with hx4|hx3|hx2|hx1|hx0|hxp1|hxp2|hxp3
  · subst x
    have heq : h+(-4:Int)=h-4 := by omega
    rw [heq]
    simpa [firstCyclePrefix22Start] using h4
  · subst x
    have heq : h+(-3:Int)=h-3 := by omega
    rw [heq]
    simpa [firstCyclePrefix22Start] using h3
  · subst x
    have heq : h+(-2:Int)=h-2 := by omega
    rw [heq]
    simpa [firstCyclePrefix22Start] using h2
  · subst x
    have heq : h+(-1:Int)=h-1 := by omega
    rw [heq]
    simpa [firstCyclePrefix22Start] using h1
  · subst x
    simpa [firstCyclePrefix22Start] using h0
  · subst x
    simpa [firstCyclePrefix22Start] using hp1
  · subst x
    simpa [firstCyclePrefix22Start] using hp2
  · subst x
    simpa [firstCyclePrefix22Start] using hp3

/-! ## The two-zero setup before the state-1 triple scan -/

/-- The exact tape update made by the state-4/state-0 two-step setup. -/
def afterFirstCycleTwoZero (T : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x=h || x=h+1 then true else T x

private theorem lookup40 :
    tm2 ((4 : Fin 6), false) = some ⟨true,true,0⟩ := by rfl

private theorem lookup00 :
    tm2 ((0 : Fin 6), false) = some ⟨true,true,1⟩ := by rfl

/-- Two consecutive zeroes are written to one and the head enters state 1. -/
theorem firstCycleTwoZeroSetup (T : Int → Bool) (h : Int)
    (h0 : T h = false) (h1 : T (h+1) = false) :
    run tm2 2 ⟨4,h,T⟩ =
      some ⟨1,h+2,afterFirstCycleTwoZero T h⟩ := by
  have hback : h+1+(-1)=h := by omega
  have hne : h+1 ≠ h := by omega
  simp [run,rawStep,readSlot,applyMove,h0,h1,hne,
    lookup40,lookup00]
  constructor
  · omega
  · funext x
    by_cases hx0 : x=h <;> by_cases hx1 : x=h+1 <;>
      simp [afterFirstCycleTwoZero,hx0,hx1]

/-! ## The four-step post-drain Q(z) bridge -/

/-- The four cells read by the fixed bridge, relative to its state-3 head. -/
def firstCyclePostludeInside (x : Int) : Bool :=
  decide (-3 ≤ x ∧ x ≤ 0)

/-- Input bits on offsets -3..0 are 0,0,1,0. -/
def firstCyclePostludeStart : FConfig :=
  ⟨3, 0, [-1]⟩

/-- Four moves end in state 4, two cells to the left, writing at offset -3. -/
def firstCyclePostludeEnd : FConfig :=
  ⟨4, -2, [-3]⟩

theorem firstCyclePostlude_exact :
    fRun tm2 4 firstCyclePostludeStart =
      some firstCyclePostludeEnd := by
  decide

theorem firstCyclePostlude_heads :
    (List.range 4).all (fun k =>
      match fRun tm2 k firstCyclePostludeStart with
      | none => true
      | some f => firstCyclePostludeInside f.head) = true := by
  decide

/-- Arbitrary-tape lift of the four-step state-3 to state-4 bridge. -/
theorem firstCyclePostlude_at (T : Int → Bool) (h : Int)
    (hinput :
      T (h-3) = false ∧
      T (h-2) = false ∧
      T (h-1) = true ∧
      T h = false) :
    run tm2 4 ⟨3,h,T⟩ =
      some (frameAt T h firstCyclePostludeInside firstCyclePostludeEnd) := by
  rcases hinput with ⟨h3,h2,h1,h0⟩
  apply bridgeAt T h firstCyclePostludeInside
    firstCyclePostludeStart firstCyclePostludeEnd 4 rfl
    firstCyclePostlude_exact firstCyclePostlude_heads
  intro x hx
  have hrange : -3 ≤ x ∧ x ≤ 0 := by
    simpa [firstCyclePostludeInside] using hx
  have hcases : x=(-3) ∨ x=(-2) ∨ x=(-1) ∨ x=0 := by omega
  rcases hcases with hx3|hx2|hx1|hx0
  · subst x
    have heq : h+(-3:Int)=h-3 := by omega
    rw [heq]
    simpa [firstCyclePostludeStart] using h3
  · subst x
    have heq : h+(-2:Int)=h-2 := by omega
    rw [heq]
    simpa [firstCyclePostludeStart] using h2
  · subst x
    have heq : h+(-1:Int)=h-1 := by omega
    rw [heq]
    simpa [firstCyclePostludeStart] using h1
  · subst x
    simpa [firstCyclePostludeStart] using h0

/-- The left sweep leaves every cell strictly before its final moving-zero
boundary unchanged. -/
private theorem sweptLeft_preserves_left (n : Nat) (T : Int → Bool)
    (h x : Int) (hx : x < h-(n:Int)+1) :
    sweptLeft n T h x = T x := by
  induction n generalizing T h with
  | zero => rfl
  | succ n ih =>
      have hrec := ih (holeThree T h) (h-1) (by omega)
      have hne0 : x ≠ h := by omega
      have hne1 : x ≠ h+1 := by omega
      have hafter : holeThree T h x = T x := by
        simp [holeThree,hne0,hne1]
      simpa [sweptLeft,hafter] using hrec

/-- Compose the existing exact counted left sweep with the four-step bridge.
The only post-sweep hypotheses concern the four cells immediately to the
left of the final head; they are unchanged by the sweep. -/
theorem firstCyclePostlude_from_sweep
    (k : Nat) (T : Int → Bool) (h : Int)
    (hones : leftOnes T h k)
    (hr : T (h+1) = false)
    (hg3 : T (h-(k:Int)-3) = false)
    (hg2 : T (h-(k:Int)-2) = false)
    (hg1 : T (h-(k:Int)-1) = true)
    (hg0 : T (h-(k:Int)) = false) :
    run tm2 (3*k+4) ⟨3,h,T⟩ =
      some (frameAt (sweptLeft k T h) (h-(k:Int))
        firstCyclePostludeInside firstCyclePostludeEnd) := by
  let g : Int := h-(k:Int)
  let U : Int → Bool := sweptLeft k T h
  have hscan :
      run tm2 (3*k) ⟨3,h,T⟩ = some ⟨3,g,U⟩ := by
    simpa [g,U] using counted_left_sweep k T h hones hr
  have hU3 : U (g-3) = false := by
    have hp := sweptLeft_preserves_left k T h (g-3) (by dsimp [g]; omega)
    change sweptLeft k T h (g-3) = false
    rw [hp]
    simpa [g] using hg3
  have hU2 : U (g-2) = false := by
    have hp := sweptLeft_preserves_left k T h (g-2) (by dsimp [g]; omega)
    change sweptLeft k T h (g-2) = false
    rw [hp]
    simpa [g] using hg2
  have hU1 : U (g-1) = true := by
    have hp := sweptLeft_preserves_left k T h (g-1) (by dsimp [g]; omega)
    change sweptLeft k T h (g-1) = true
    rw [hp]
    simpa [g] using hg1
  have hU0 : U g = false := by
    have hp := sweptLeft_preserves_left k T h g (by dsimp [g]; omega)
    change sweptLeft k T h g = false
    rw [hp]
    simpa [g] using hg0
  have hbridge := firstCyclePostlude_at U g ⟨hU3,hU2,hU1,hU0⟩
  rw [run_append,hscan]
  simp only [Option.bind_some]
  simpa [g,U] using hbridge

/-- The exact post-drain cost for the first positive-z q4 cycle. -/
theorem firstCyclePostlude_cost (z : Nat) :
    3*(3*(2^z-1)+3*z+7)+4 = 9*2^z+9*z+16 := by
  have hpow : 1 ≤ 2^z := by
    have hpos : 0 < 2^z := Nat.pow_pos (by decide)
    omega
  omega

/-- The Q(z) source macro, isolated from the preceding prefix and drain.
The S0 drain output supplies a contiguous run of k left-facing ones,
a zero at the first right cell, and the fixed 0,0,1,0 four-cell bridge
pattern at absolute cells 0..3. -/
theorem firstCycleQ_from_S0Input
    (z : Nat) (T : Int → Bool) (h : Int)
    (hh : h = (3*2^z+3*z+7 : Int))
    (hleft : leftOnes T h (3*(2^z-1)+3*z+7))
    (hr : T (h+1) = false)
    (h0 : T 0 = false)
    (h1 : T 1 = false)
    (h2 : T 2 = true)
    (h3 : T 3 = false) :
    run tm2 (9*2^z+9*z+16) ⟨3,h,T⟩ =
      some (frameAt
        (sweptLeft (3*(2^z-1)+3*z+7) T h) 3
        firstCyclePostludeInside firstCyclePostludeEnd) := by
  let k : Nat := 3*(2^z-1)+3*z+7
  have hpow : 1 ≤ 2^z := by
    have hpos : 0 < 2^z := Nat.pow_pos (by decide)
    omega
  have hsub : ((2^z - 1 : Nat) : Int) = (2^z : Int) - 1 := by
    rw [Nat.cast_sub hpow]
    rfl
  have hhead : h-(k:Int)=3 := by
    dsimp [k]
    rw [hh]
    omega
  have hg3 : T (h-(k:Int)-3) = false := by
    simpa [hhead] using h0
  have hg2 : T (h-(k:Int)-2) = false := by
    simpa [hhead] using h1
  have hg1 : T (h-(k:Int)-1) = true := by
    simpa [hhead] using h2
  have hg0 : T (h-(k:Int)) = false := by
    simpa [hhead] using h3
  have hrun := firstCyclePostlude_from_sweep k T h hleft hr hg3 hg2 hg1 hg0
  have hcost : 3*k+4 = 9*2^z+9*z+16 := by
    dsimp [k]
    omega
  rw [← hcost]
  simpa [k,hhead] using hrun

#print axioms firstCyclePrefix22_exact
#print axioms firstCyclePrefix22_heads
#print axioms firstCyclePrefix22_at
#print axioms firstCycleTwoZeroSetup
#print axioms firstCyclePostlude_exact
#print axioms firstCyclePostlude_heads
#print axioms firstCyclePostlude_at
#print axioms firstCyclePostlude_from_sweep
#print axioms firstCycleQ_from_S0Input

end BB6Coverage.Agent48PositiveZFirstCycle
