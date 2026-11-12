import ChampionRootBridge
import S1Encoder
import UniformTM63
import Lean.Elab.Tactic.Omega

/-!
# Exact S0/BinDec endpoint alignment with Agent 26's uniform zipper

This file does not re-prove the all-valuation TM63 count.  It identifies the
source-facing S0 configuration from S1Encoder with the exact finite-zipper
rawStart/rawEnd configurations in TM63Uniform.counted_all.  The only padding
difference is three explicit blank guard cells on the zipper's right tail.
-/

namespace BB6Coverage.Agent48UniformBridge

open BB6Coverage
open BB6Coverage.Agent8S1Encoder

/-- Interpret a nearest-first zipper at an arbitrary physical head position. -/
def uniformTapeAt (c : TM63Uniform.Cfg) (h : Int) : Int → Bool :=
  fun x =>
    if x ≤ h then
      sideBit (c.h :: c.l) (Int.toNat (h-x))
    else
      sideBit c.r (Int.toNat (x-h-1))

/-- All relevant zipper endpoints are in D, so their source Config is direct. -/
def uniformConfigAt3 (h : Int) (c : TM63Uniform.Cfg) : Config :=
  ⟨(3 : Fin 6), h, uniformTapeAt c h⟩

theorem d1pow_eq_uniformOnes (n : Nat) :
    d1pow n = TM63Uniform.ones (3*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change d1 ++ d1pow n = TM63Uniform.ones (3*(n+1))
      rw [show 3*(n+1) = 3+3*n by omega, TM63Uniform.ones_add]
      simp [d1, TM63Uniform.ones, ih]

theorem tri_eq_d0pow (n : Nat) :
    TM63Uniform.tri n = d0pow n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [TM63Uniform.tri, d0pow, d0, ih]

theorem dTail_empty (c : Nat) :
    TM63Uniform.dTail c [] = d1pow (c+1) ++ [false,false,false] := by
  simp only [TM63Uniform.dTail, List.append_nil]
  rw [← d1pow_eq_uniformOnes (c+1)]

/-- The head plus the zipper's left list is exactly d1^k d0 and its
arbitrary residual source prefix. -/
theorem rawStart_left (k c : Nat) (ls rs : List Bool) :
    (TM63Uniform.rawStart k c ls rs).h ::
      (TM63Uniform.rawStart k c ls rs).l =
        d1pow k ++ d0 ++ ls := by
  cases k with
  | zero =>
      simp [TM63Uniform.rawStart, TM63Uniform.dBoundary, d0, d1pow, List.append_assoc]
  | succ k =>
      change (true :: TM63Uniform.ones (3*k+2)) ++ [false,false,true] ++ ls =
        d1pow (k+1) ++ d0 ++ ls
      have hone : true :: TM63Uniform.ones (3*k+2) = d1pow (k+1) := by
        rw [d1pow_eq_uniformOnes]
        have hpow : 3*(k+1) = (3*k+2)+1 := by omega
        rw [hpow]
        rfl
      rw [hone]
      rfl

/-- rawStart has the S0 right word plus the three explicit blank guards
required by the finite-zipper theorem. -/
theorem rawStart_right (k c : Nat) (ls : List Bool) :
    (TM63Uniform.rawStart k c ls []).r =
      s0RightFacing c ++ [false,false,false] := by
  cases k with
  | zero =>
      simp only [TM63Uniform.rawStart, TM63Uniform.dBoundary]
      rw [dTail_empty]
      simp [s0RightFacing, d1, TM63Uniform.ones, List.append_assoc]
  | succ k =>
      simp only [TM63Uniform.rawStart]
      rw [dTail_empty]
      simp [s0RightFacing, d1, List.append_assoc]

/-- The head plus rawEnd's left list is d0^k d1 and the same exterior. -/
theorem rawEnd_left (k c : Nat) (ls : List Bool) :
    (TM63Uniform.rawEnd k c ls []).h ::
      (TM63Uniform.rawEnd k c ls []).l =
        d0pow k ++ d1 ++ ls := by
  cases k with
  | zero =>
      simp [TM63Uniform.rawEnd, d0pow, d1, List.append_assoc]
  | succ k =>
      simp only [TM63Uniform.rawEnd]
      rw [tri_eq_d0pow]
      simp [d0pow, d0, d1, List.append_assoc]

/-- rawEnd's right word is exactly the next S0 unary counter. -/
theorem rawEnd_right (k c : Nat) (ls : List Bool) :
    (TM63Uniform.rawEnd k c ls []).r = s0RightFacing (c+1) := by
  cases k with
  | zero =>
      simp only [TM63Uniform.rawEnd, TM63Uniform.scoredRight, s0RightFacing, List.append_nil]
      rw [d1pow_eq_uniformOnes]
      rw [show 3*(c+1+1) = 3*(c+2) by omega]
      rfl
  | succ k =>
      simp only [TM63Uniform.rawEnd, TM63Uniform.scoredRight, s0RightFacing, List.append_nil]
      rw [d1pow_eq_uniformOnes]
      rw [show 3*(c+1+1) = 3*(c+2) by omega]
      rfl

theorem sideBit_false_of_all_false (xs : List Bool) :
    (∀ b ∈ xs, b = false) → ∀ i, sideBit xs i = false := by
  induction xs with
  | nil =>
      intro hxs i
      simp [sideBit]
  | cons b bs ih =>
      intro hxs i
      have hb : b = false := hxs b (by simp)
      have hbs : ∀ x ∈ bs, x = false := by
        intro x hx
        exact hxs x (by simp [hx])
      cases i with
      | zero => simp [sideBit, hb]
      | succ i => exact ih hbs i

theorem sideBit_append_false_suffix (xs ys : List Bool) :
    (∀ b ∈ ys, b = false) →
    ∀ i, sideBit (xs ++ ys) i = sideBit xs i := by
  induction xs with
  | nil =>
      intro hys i
      simpa [sideBit] using sideBit_false_of_all_false ys hys i
  | cons x xs ih =>
      intro hys i
      cases i with
      | zero => rfl
      | succ i => exact ih hys i

private theorem three_false_suffix :
    ∀ b ∈ [false,false,false], b = false := by
  intro b hb
  simpa using hb

/-- Every source S0 input with z=(2q+1)2^k is exactly the all-k
finite-zipper rawStart, embedded at the same absolute head. -/
theorem s0Config_eq_uniformRawStart
    (l : List Bool) (len q k c : Nat) (h : Int)
    (hq : q < 2^len) :
    s0Config l (len+1+k) ((2*q+1)*2^k) c h =
      uniformConfigAt3 h
        (TM63Uniform.rawStart k c (binDec len q ++ l) []) := by
  let ls := binDec len q ++ l
  have hleft :
      (TM63Uniform.rawStart k c ls []).h ::
        (TM63Uniform.rawStart k c ls []).l =
          s0LeftFacing l (len+1+k) ((2*q+1)*2^k) := by
    rw [s0LeftFacing_carryPrefix l len q k hq]
    simpa [ls] using rawStart_left k c ls []
  have hright : ∀ i,
      sideBit (TM63Uniform.rawStart k c ls []).r i =
        sideBit (s0RightFacing c) i := by
    intro i
    rw [rawStart_right]
    exact sideBit_append_false_suffix (s0RightFacing c)
      [false,false,false] three_false_suffix i
  apply congrArg (fun t : Int → Bool => (⟨(3 : Fin 6), h, t⟩ : Config))
  funext x
  by_cases hx : x ≤ h
  · change s0Tape l (len+1+k) ((2*q+1)*2^k) c h x =
      uniformTapeAt (TM63Uniform.rawStart k c ls []) h x
    simp only [s0Tape, uniformTapeAt, if_pos hx]
    rw [← hleft]
  · change s0Tape l (len+1+k) ((2*q+1)*2^k) c h x =
      uniformTapeAt (TM63Uniform.rawStart k c ls []) h x
    simp only [s0Tape, uniformTapeAt, if_neg hx]
    rw [← hright (Int.toNat (x-h-1))]

/-- Every source S0 post-decrement configuration is exactly Agent 26's
all-k rawEnd, with the right unary counter increased by one. -/
theorem s0Config_eq_uniformRawEnd
    (l : List Bool) (len q k c : Nat) (h : Int)
    (hq : q < 2^len) :
    s0Config l (len+1+k) (((2*q+1)*2^k)-1) (c+1) h =
      uniformConfigAt3 h
        (TM63Uniform.rawEnd k c (binDec len q ++ l) []) := by
  let ls := binDec len q ++ l
  have hleft :
      (TM63Uniform.rawEnd k c ls []).h ::
        (TM63Uniform.rawEnd k c ls []).l =
          s0LeftFacing l (len+1+k) (((2*q+1)*2^k)-1) := by
    change (TM63Uniform.rawEnd k c ls []).h ::
      (TM63Uniform.rawEnd k c ls []).l =
        binDec (len+1+k) (((2*q+1)*2^k)-1) ++ l
    rw [binDec_sub_one_carryPrefix len q k hq]
    simpa [ls] using rawEnd_left k c ls
  have hright : ∀ i,
      sideBit (TM63Uniform.rawEnd k c ls []).r i =
        sideBit (s0RightFacing (c+1)) i := by
    intro i
    rw [rawEnd_right]
  apply congrArg (fun t : Int → Bool => (⟨(3 : Fin 6), h, t⟩ : Config))
  funext x
  by_cases hx : x ≤ h
  · change s0Tape l (len+1+k) (((2*q+1)*2^k)-1) (c+1) h x =
      uniformTapeAt (TM63Uniform.rawEnd k c ls []) h x
    simp only [s0Tape, uniformTapeAt, if_pos hx]
    rw [← hleft]
  · change s0Tape l (len+1+k) (((2*q+1)*2^k)-1) (c+1) h x =
      uniformTapeAt (TM63Uniform.rawEnd k c ls []) h x
    simp only [s0Tape, uniformTapeAt, if_neg hx]
    rw [← hright (Int.toNat (x-h-1))]

#print axioms s0Config_eq_uniformRawStart
#print axioms s0Config_eq_uniformRawEnd

end BB6Coverage.Agent48UniformBridge
