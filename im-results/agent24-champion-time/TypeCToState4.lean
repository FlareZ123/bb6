import PositiveZTypeCBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent24TypeCContinuation

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent48PositiveZTypeC
open BB6Coverage.Agent48PositiveZFirstCycle
open BB6Coverage.Agent48PositiveZSecondCycle

/-- The 11-step continuation after the Type-C 35-step prefix reads
ten consecutive ones and the following blank. -/
def typeCPostSetupInside (x : Int) : Bool :=
  decide (0 ≤ x ∧ x ≤ 10)

def typeCPostSetupStart : FConfig :=
  ⟨1, 0, [0,1,2,3,4,5,6,7,8,9]⟩

def typeCPostSetupEnd : FConfig :=
  ⟨4, 11, [10,8,5,2]⟩

theorem typeCPostSetup_exact :
    fRun tm2 11 typeCPostSetupStart = some typeCPostSetupEnd := by
  decide

theorem typeCPostSetup_heads :
    (List.range 11).all (fun k =>
      match fRun tm2 k typeCPostSetupStart with
      | none => true
      | some f => typeCPostSetupInside f.head) = true := by
  decide

/-- Arbitrary-tape lift of the 11-step state-1 to state-4 bridge. -/
theorem typeCPostSetup_at (T : Int → Bool) (k : Int)
    (hones : ∀ i : Nat, i < 10 → T (k+(i:Int)) = true)
    (hblank : T (k+10) = false) :
    run tm2 11 ⟨1,k,T⟩ =
      some (frameAt T k typeCPostSetupInside typeCPostSetupEnd) := by
  apply bridgeAt T k typeCPostSetupInside
    typeCPostSetupStart typeCPostSetupEnd 11 rfl
    typeCPostSetup_exact typeCPostSetup_heads
  intro x hx
  have hcases :
      x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 ∨
      x=6 ∨ x=7 ∨ x=8 ∨ x=9 ∨ x=10 := by
    have hrange : 0 ≤ x ∧ x ≤ 10 := by
      simpa [typeCPostSetupInside] using hx
    omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4|hx5|hx6|hx7|hx8|hx9|hx10
  · subst x
    simpa [typeCPostSetupStart] using hones 0 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 1 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 2 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 3 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 4 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 5 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 6 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 7 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 8 (by omega)
  · subst x
    simpa [typeCPostSetupStart] using hones 9 (by omega)
  · subst x
    have heq : k+(10:Int) = k+10 := by rfl
    rw [heq]
    simp [typeCPostSetupStart]
    exact hblank

/-- Tape after the existing 35-step Type-C bridge and two-zero setup. -/
def typeCPostSetupTape (T : Int → Bool) (h : Int) : Int → Bool :=
  afterFirstCycleTwoZero
    (frameAt T h typeCInside typeCEnd).tape (h-9)

theorem typeCPostSetupTape_ones (T : Int → Bool) (h : Int) :
    ∀ i : Nat, i < 10 →
      typeCPostSetupTape T h (h-7+(i:Int)) = true := by
  intro i hi
  have hne0 : h-7+(i:Int) ≠ h-9 := by omega
  have hne1 : h-7+(i:Int) ≠ h-9+1 := by omega
  have hcases :
      i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
      i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by omega
  have hmem : -7+(i:Int) ∈ typeCEnd.marked := by
    rcases hcases with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9
    all_goals subst i <;> simp [typeCEnd]
  have hinside : typeCInside (-7+(i:Int)) = true := by
    simp [typeCInside]
    omega
  have hcoord : h-7+(i:Int)-h = -7+(i:Int) := by omega
  simp [typeCPostSetupTape,afterFirstCycleTwoZero,hne0,hne1,
    frameAt_tape,hinside,hmem,hcoord]

theorem typeCPostSetupTape_blank (T : Int → Bool) (h : Int)
    (h3 : T (h+3) = false) :
    typeCPostSetupTape T h (h+3) = false := by
  have hcond : ¬ (h+3 = h-9 ∨ h+3 = h-9+1) := by omega
  have hcoord : h+3-h = 3 := by omega
  simp [typeCPostSetupTape,afterFirstCycleTwoZero,hcond,
    frameAt_tape,typeCInside,hcoord,h3]

/-- The complete 46-step Type-C prefix reaches state 4 at h+4. -/
theorem typeC_to_state4 (T : Int → Bool) (h : Int)
    (hin : typeCInput T h) (h3 : T (h+3) = false) :
    run tm2 46 ⟨4,h,T⟩ =
      some (frameAt (typeCPostSetupTape T h) (h-7)
        typeCPostSetupInside typeCPostSetupEnd) := by
  have h35 := typeC_two_step_continuation T h hin
  have hones := typeCPostSetupTape_ones T h
  have hblank := typeCPostSetupTape_blank T h h3
  have hblank' : typeCPostSetupTape T h ((h-7)+10) = false := by
    have heq : (h-7)+10 = h+3 := by omega
    rw [heq]
    exact hblank
  have h11 := typeCPostSetup_at (typeCPostSetupTape T h)
    (h-7) hones hblank'
  calc
    run tm2 46 ⟨4,h,T⟩ =
        (run tm2 35 ⟨4,h,T⟩).bind (fun c => run tm2 11 c) := by
          rw [show 46 = 35+11 by omega, run_append]
    _ = run tm2 11 ⟨1,h-7,typeCPostSetupTape T h⟩ := by
          rw [h35]
          rfl
    _ = some (frameAt (typeCPostSetupTape T h) (h-7)
          typeCPostSetupInside typeCPostSetupEnd) := h11

/-- The 46-step Type-C prefix leaves the entire right tail at h+4
and beyond unchanged. -/
theorem typeC_to_state4_preserves_after
    (T : Int → Bool) (h x : Int) (hx : h+4 ≤ x) :
    (frameAt (typeCPostSetupTape T h) (h-7)
      typeCPostSetupInside typeCPostSetupEnd).tape x = T x := by
  have hfinal :
      (frameAt (typeCPostSetupTape T h) (h-7)
        typeCPostSetupInside typeCPostSetupEnd).tape x =
        typeCPostSetupTape T h x := by
    rw [frameAt_tape]
    have houtside : typeCPostSetupInside (x-(h-7)) = false := by
      simp [typeCPostSetupInside]
      omega
    simp [houtside]
  have hU : typeCPostSetupTape T h x = T x := by
    have hcond : ¬ (x = h-9 ∨ x = h-9+1) := by omega
    have houtside : typeCInside (x-h) = false := by
      simp [typeCInside]
      omega
    simp [typeCPostSetupTape,afterFirstCycleTwoZero,hcond,
      frameAt_tape,houtside]
  exact hfinal.trans hU

/-- The third right-side zero in the Type-C checkpoint is the blank
needed by the 11-step continuation. The left side is arbitrary. -/
theorem typeC_right_guard_from_sides
    (left tailR : List Bool) (h : Int) :
    (q4TapeFromSides left ([false,false,false] ++ tailR) h) (h+3) = false := by
  let right : List Bool := [false,false,false] ++ tailR
  let T : Int → Bool := q4TapeFromSides left right h
  have hright (i : Nat) (hi : i < 3) :
      T (h+1+(i:Int)) = sideBit right i := by
    have hgt : ¬ h+1+(i:Int) ≤ h := by omega
    have hcoord : Int.toNat ((h+1+(i:Int))-h-1) = i := by omega
    unfold T q4TapeFromSides
    rw [if_neg hgt,hcoord]
  have hside : sideBit right 2 = false := by
    simp [right,sideBit]
  have hcell := (hright 2 (by omega)).trans hside
  have heq : h+1+(2:Int) = h+3 := by omega
  simpa [heq] using hcell

/-- Original-source 46-step transition for the complete M-4 checkpoint
family, with arbitrary exterior right tail. -/
theorem typeC_source_to_state4
    (A L : Nat) (tailR : List Bool) (h : Int)
    (hA : 3 ≤ A) :
    let T := q4TapeFromSides
      ([false,true,true] ++
        binDec (A+L+2) (2^A*(2^(L+2)-1)-4))
      ([false,false,false] ++ tailR) h
    run tm2 46 ⟨4,h,T⟩ =
      some (frameAt (typeCPostSetupTape T h) (h-7)
        typeCPostSetupInside typeCPostSetupEnd) := by
  let T : Int → Bool := q4TapeFromSides
    ([false,true,true] ++
      binDec (A+L+2) (2^A*(2^(L+2)-1)-4))
    ([false,false,false] ++ tailR) h
  have hin := typeC_input_from_binDec A L tailR h hA
  have h3 := typeC_right_guard_from_sides
    ([false,true,true] ++
      binDec (A+L+2) (2^A*(2^(L+2)-1)-4)) tailR h
  exact typeC_to_state4 T h hin h3

#print axioms typeCPostSetup_exact
#print axioms typeCPostSetup_heads
#print axioms typeCPostSetup_at
#print axioms typeC_to_state4
#print axioms typeC_source_to_state4

end BB6Coverage.Agent24TypeCContinuation
