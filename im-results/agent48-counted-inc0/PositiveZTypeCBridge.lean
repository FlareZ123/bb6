import PositiveZSecondCycleBridge
import PositiveZFirstCycleBridges
import Lean.Elab.Tactic.Omega

/-!
# Positive-z type-C q4 checkpoint bridge

This module certifies the 33-step transition from the third q4 checkpoint
family.  The local finite trace is an exact computation of the original
TM63 table, lifted to arbitrary exterior tape by the existing bridgeAt
theorem.  The source-side BinDec lemma identifies the required local window
when the checkpoint counter is M-4 and M=2^A(2^(L+2)-1), A>=3.

Important correction: the 33-step endpoint has an additional written one
at the far-left boundary.  At the final state-4 head, both the head cell
and its immediate right neighbour are zero.  The next two steps therefore
continue to state 1; this is not a two-step halt.
-/

namespace BB6Coverage.Agent48PositiveZTypeC

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48PositiveZSecondCycle
open BB6Coverage.Agent48PositiveZFirstCycle

/-- The 33-step bridge reads offsets -10 through 2 around its initial head. -/
def typeCInside (x : Int) : Bool :=
  decide (-10 ≤ x ∧ x ≤ 2)

/-- At head h, the input word on h-10,...,h+2 is 00 11111111 000. -/
def typeCInput (T : Int → Bool) (h : Int) : Prop :=
  T (h-10) = false ∧
  T (h-9) = false ∧
  T (h-8) = true ∧
  T (h-7) = true ∧
  T (h-6) = true ∧
  T (h-5) = true ∧
  T (h-4) = true ∧
  T (h-3) = true ∧
  T (h-2) = true ∧
  T (h-1) = true ∧
  T h = false ∧
  T (h+1) = false ∧
  T (h+2) = false

def typeCStart : FConfig :=
  ⟨4, 0, [-8,-7,-6,-5,-4,-3,-2,-1]⟩

/-- Exact endpoint: the final head is at h-9.  The cell h-10 is also
written, in addition to the ten-cell one-run h-7,...,h+2. -/
def typeCEnd : FConfig :=
  ⟨4, -9, [-10,-7,-6,-5,-4,-3,-2,-1,0,1,2]⟩

theorem typeC_exact :
    fRun tm2 33 typeCStart = some typeCEnd := by
  decide

theorem typeC_heads :
    (List.range 33).all (fun k =>
      match fRun tm2 k typeCStart with
      | none => true
      | some f => typeCInside f.head) = true := by
  decide

/-- Arbitrary-tape lift of the exact type-C 33-step trace. -/
theorem typeC_at (T : Int → Bool) (h : Int)
    (hin : typeCInput T h) :
    run tm2 33 ⟨4,h,T⟩ =
      some (frameAt T h typeCInside typeCEnd) := by
  rcases hin with
    ⟨h10,h9,h8,h7,h6,h5,h4,h3,h2,h1,h0,hp1,hp2⟩
  apply bridgeAt T h typeCInside typeCStart typeCEnd 33 rfl
    typeC_exact typeC_heads
  intro x hx
  have hrange : -10 ≤ x ∧ x ≤ 2 := by
    simpa [typeCInside] using hx
  have hcases :
      x=(-10) ∨ x=(-9) ∨ x=(-8) ∨ x=(-7) ∨ x=(-6) ∨
      x=(-5) ∨ x=(-4) ∨ x=(-3) ∨ x=(-2) ∨ x=(-1) ∨
      x=0 ∨ x=1 ∨ x=2 := by omega
  rcases hcases with
    hx10|hx9|hx8|hx7|hx6|hx5|hx4|hx3|hx2|hx1|hx0|hxp1|hxp2
  · have heq : h+(-10:Int) = h-10 := by omega
    rw [heq]
    simpa [typeCStart] using h10
  · have heq : h+(-9:Int) = h-9 := by omega
    rw [heq]
    simpa [typeCStart] using h9
  · have heq : h+(-8:Int) = h-8 := by omega
    rw [heq]
    simpa [typeCStart] using h8
  · have heq : h+(-7:Int) = h-7 := by omega
    rw [heq]
    simpa [typeCStart] using h7
  · have heq : h+(-6:Int) = h-6 := by omega
    rw [heq]
    simpa [typeCStart] using h6
  · have heq : h+(-5:Int) = h-5 := by omega
    rw [heq]
    simpa [typeCStart] using h5
  · have heq : h+(-4:Int) = h-4 := by omega
    rw [heq]
    simpa [typeCStart] using h4
  · have heq : h+(-3:Int) = h-3 := by omega
    rw [heq]
    simpa [typeCStart] using h3
  · have heq : h+(-2:Int) = h-2 := by omega
    rw [heq]
    simpa [typeCStart] using h2
  · have heq : h+(-1:Int) = h-1 := by omega
    rw [heq]
    simpa [typeCStart] using h1
  · simpa [typeCStart] using h0
  · simpa [typeCStart] using hp1
  · simpa [typeCStart] using hp2

/-- The third checkpoint's head-facing prefix is 011 followed by two
all-one BinDec digits and one zero digit. -/
theorem typeC_input_from_sides (tailL tailR : List Bool) (h : Int) :
    typeCInput
      (q4TapeFromSides
        ([false,true,true] ++ d1 ++ d1 ++ d0 ++ tailL)
        ([false,false,false] ++ tailR) h) h := by
  let left : List Bool := [false,true,true] ++ d1 ++ d1 ++ d0 ++ tailL
  let right : List Bool := [false,false,false] ++ tailR
  let T : Int → Bool := q4TapeFromSides left right h
  have hleft (i : Nat) (hi : i ≤ 10) :
      T (h-(i:Int)) = sideBit left i := by
    have hle : h-(i:Int) ≤ h := by omega
    have hcoord : Int.toNat (h-(h-(i:Int))) = i := by omega
    unfold T q4TapeFromSides
    rw [if_pos hle, hcoord]
  have hright (i : Nat) (hi : i < 3) :
      T (h+1+(i:Int)) = sideBit right i := by
    have hgt : ¬ h+1+(i:Int) ≤ h := by omega
    have hcoord : Int.toNat ((h+1+(i:Int))-h-1) = i := by omega
    unfold T q4TapeFromSides
    rw [if_neg hgt, hcoord]
  have hs0 : sideBit left 0 = false := by simp [left,sideBit,d1,d0]
  have hs1 : sideBit left 1 = true := by simp [left,sideBit,d1,d0]
  have hs2 : sideBit left 2 = true := by simp [left,sideBit,d1,d0]
  have hs3 : sideBit left 3 = true := by simp [left,sideBit,d1,d0]
  have hs4 : sideBit left 4 = true := by simp [left,sideBit,d1,d0]
  have hs5 : sideBit left 5 = true := by simp [left,sideBit,d1,d0]
  have hs6 : sideBit left 6 = true := by simp [left,sideBit,d1,d0]
  have hs7 : sideBit left 7 = true := by simp [left,sideBit,d1,d0]
  have hs8 : sideBit left 8 = true := by simp [left,sideBit,d1,d0]
  have hs9 : sideBit left 9 = false := by simp [left,sideBit,d1,d0]
  have hs10 : sideBit left 10 = false := by simp [left,sideBit,d1,d0]
  have hr0 : sideBit right 0 = false := by simp [right,sideBit]
  have hr1 : sideBit right 1 = false := by simp [right,sideBit]
  change T (h-10) = false ∧ T (h-9) = false ∧
    T (h-8) = true ∧ T (h-7) = true ∧ T (h-6) = true ∧
    T (h-5) = true ∧ T (h-4) = true ∧ T (h-3) = true ∧
    T (h-2) = true ∧ T (h-1) = true ∧ T h = false ∧
    T (h+1) = false ∧ T (h+2) = false
  exact ⟨by simpa using (hleft 10 (by omega)).trans hs10,
    by simpa using (hleft 9 (by omega)).trans hs9,
    by simpa using (hleft 8 (by omega)).trans hs8,
    by simpa using (hleft 7 (by omega)).trans hs7,
    by simpa using (hleft 6 (by omega)).trans hs6,
    by simpa using (hleft 5 (by omega)).trans hs5,
    by simpa using (hleft 4 (by omega)).trans hs4,
    by simpa using (hleft 3 (by omega)).trans hs3,
    by simpa using (hleft 2 (by omega)).trans hs2,
    by simpa using (hleft 1 (by omega)).trans hs1,
    by simpa using (hleft 0 (by omega)).trans hs0,
    by simpa using (hright 0 (by omega)).trans hr0,
    by
      have hstepRight := (hright 1 (by omega)).trans hr1
      simpa [show h+1+(1:Int) = h+2 by omega] using hstepRight

/-- For A>=3, the authentic marker counter M=2^A(2^(L+2)-1)
satisfies BinDec(M-4)=d1 d1 d0 followed by an arbitrary quotient tail. -/
theorem typeC_binDec_prefix (A L : Nat) (hA : 3 ≤ A) :
    binDec (A+L+2) (2^A*(2^(L+2)-1)-4) =
      d1 ++ d1 ++ d0 ++
        binDec (A+L-1) (2^(A-3)*(2^(L+2)-1)-1) := by
  let q : Nat := 2^(A-3)*(2^(L+2)-1)-1
  have h22 : 2^2 = 4 := by decide
  have hA3eq : A-2 = (A-3)+1 := by omega
  have hpowA2 : 2^(A-2) = 2*2^(A-3) := by
    calc
      2^(A-2) = 2^((A-3)+1) := congrArg (fun n => 2^n) hA3eq
      _ = 2^(A-3)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(A-3) := by ac_rfl
  have hAeq : A = (A-2)+2 := by omega
  have hpowA : 2^A = 4*2^(A-2) := by
    calc
      2^A = 2^((A-2)+2) := congrArg (fun n => 2^n) hAeq
      _ = 2^(A-2)*2^2 := by rw [Nat.pow_add]
      _ = 4*2^(A-2) := by rw [h22]; ac_rfl
  have hOpos : 0 < 2^(L+2)-1 := by
    have hpow : 4 ≤ 2^(L+2) := by
      simpa [h22] using
        (Nat.pow_le_pow_right (by decide : 2 > 0) (show 2 ≤ L+2 by omega))
    omega
  have hfactor :
      2*q+1 = 2^(A-2)*(2^(L+2)-1)-1 := by
    dsimp [q]
    rw [hpowA2]
    have hmul : (2*2^(A-3))*(2^(L+2)-1) =
        2*(2^(A-3)*(2^(L+2)-1)) := by ac_rfl
    rw [hmul]
    omega
  have hval :
      2^A*(2^(L+2)-1)-4 = (2*q+1)*2^2 := by
    calc
      2^A*(2^(L+2)-1)-4 =
          (4*2^(A-2))*(2^(L+2)-1)-4 := by rw [hpowA]
      _ = 4*(2^(A-2)*(2^(L+2)-1))-4 := by ac_rfl
      _ = 4*(2^(A-2)*(2^(L+2)-1)-1) := by
        have hp : 0 < 2^(A-2)*(2^(L+2)-1) :=
          Nat.mul_pos (Nat.pow_pos (by decide)) hOpos
        omega
      _ = 4*(2*q+1) := by rw [hfactor]
      _ = (2*q+1)*2^2 := by rw [h22]; ac_rfl
  have hALeq : A+L-1 = (A-3)+(L+2) := by omega
  have hpow :
      2^(A+L-1) = 2^(A-3)*2^(L+2) := by
    calc
      2^(A+L-1) = 2^((A-3)+(L+2)) := congrArg (fun n => 2^n) hALeq
      _ = 2^(A-3)*2^(L+2) := by rw [Nat.pow_add]
  have hlt : 2^(L+2)-1 < 2^(L+2) :=
    Nat.sub_lt (Nat.pow_pos (by decide)) (by decide)
  have hprod :
      2^(A-3)*(2^(L+2)-1) < 2^(A+L-1) := by
    calc
      2^(A-3)*(2^(L+2)-1) < 2^(A-3)*2^(L+2) :=
        Nat.mul_lt_mul_of_pos_left hlt (Nat.pow_pos (by decide))
      _ = 2^(A+L-1) := hpow.symm
  have hq : q < 2^(A+L-1) := by
    dsimp [q]
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hprod
  have hlen : A+L+2 = (A+L-1)+1+2 := by omega
  rw [hlen,hval]
  simpa [d1pow,List.append_assoc,q] using
    (binDec_carryPrefix (A+L-1) q 2 hq)

/-- Source input theorem for the type-C checkpoint side streams. -/
theorem typeC_input_from_binDec
    (A L : Nat) (tailR : List Bool) (h : Int)
    (hA : 3 ≤ A) :
    typeCInput
      (q4TapeFromSides
        ([false,true,true] ++
          binDec (A+L+2) (2^A*(2^(L+2)-1)-4))
        ([false,false,false] ++ tailR) h) h := by
  rw [typeC_binDec_prefix A L hA]
  exact typeC_input_from_sides
    (binDec (A+L-1) (2^(A-3)*(2^(L+2)-1)-1)) tailR h

/-- Original-source 33-step transition for the complete M-4 checkpoint
family, with no restriction on either exterior tape tail. -/
theorem typeC_source_bridge
    (A L : Nat) (tailR : List Bool) (h : Int)
    (hA : 3 ≤ A) :
    let T := q4TapeFromSides
      ([false,true,true] ++
        binDec (A+L+2) (2^A*(2^(L+2)-1)-4))
      ([false,false,false] ++ tailR) h
    run tm2 33 ⟨4,h,T⟩ =
      some (frameAt T h typeCInside typeCEnd) := by
  let T : Int → Bool := q4TapeFromSides
    ([false,true,true] ++
      binDec (A+L+2) (2^A*(2^(L+2)-1)-4))
    ([false,false,false] ++ tailR) h
  have hin := typeC_input_from_binDec A L tailR h hA
  exact typeC_at T h hin

/-- The corrected output has two consecutive zeroes at the new q4 head:
the head cell h-9 and its right neighbour h-8 are both blank. -/
theorem typeC_output_cells (T : Int → Bool) (h : Int) :
    (frameAt T h typeCInside typeCEnd).tape (h-9) = false ∧
    (frameAt T h typeCInside typeCEnd).tape (h-8) = false ∧
    (frameAt T h typeCInside typeCEnd).tape (h-7) = true := by
  simp [frameAt_tape,typeCInside,typeCEnd]

/-- After the 33-step type-C bridge, the two zeroes trigger the ordinary
state-4/state-0 setup and continue to state 1.  This explicitly rules out
the previously suggested immediate two-step halt. -/
theorem typeC_two_step_continuation
    (T : Int → Bool) (h : Int) (hin : typeCInput T h) :
    run tm2 35 ⟨4,h,T⟩ =
      some (⟨1,h-7,
        afterFirstCycleTwoZero
          (frameAt T h typeCInside typeCEnd).tape (h-9)⟩ : Config) := by
  let U : Int → Bool := (frameAt T h typeCInside typeCEnd).tape
  have hbridge := typeC_at T h hin
  obtain ⟨hzero0,hzero1,_⟩ := typeC_output_cells T h
  have hframe : frameAt T h typeCInside typeCEnd = ⟨4,h-9,U⟩ := by
    apply config_ext
    · simp [frameAt_state,typeCEnd]
    · simp [frameAt_head,typeCEnd] <;> omega
    · rfl
  have hsetup := firstCycleTwoZeroSetup U (h-9) hzero0 hzero1
  calc
    run tm2 35 ⟨4,h,T⟩ =
        (run tm2 33 ⟨4,h,T⟩).bind (fun c => run tm2 2 c) := by
          rw [show 35 = 33+2 by omega, run_append]
    _ = run tm2 2 (frameAt T h typeCInside typeCEnd) := by
          rw [hbridge]
          rfl
    _ = some (⟨1,h-7,
          afterFirstCycleTwoZero U (h-9)⟩ : Config) := by
          rw [hframe] at hsetup
          simpa [show (h-9)+(2:Int) = h-7 by omega] using hsetup

#print axioms typeC_exact
#print axioms typeC_heads
#print axioms typeC_at
#print axioms typeC_binDec_prefix
#print axioms typeC_input_from_binDec
#print axioms typeC_source_bridge
#print axioms typeC_two_step_continuation

end BB6Coverage.Agent48PositiveZTypeC
