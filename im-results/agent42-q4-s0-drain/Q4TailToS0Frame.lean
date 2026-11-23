import Q4Suffix
import D0SweepLeftFacing
import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Generic q4Tail-to-S0 frame identity

This isolates the exact frame-to-S0 conversion needed after a counted
d1-block sweep and q4Tail.  It is deliberately parameterized by the
entire residual left stream and the far-right blank ray: those are the
only source-specific obligations left for the authentic P2/root instance.

The left counter is forced to d0pow (n-1) by D0SweepLeftFacing.
The q4Tail frame supplies exactly s0RightFacing 0 on the right.
-/

namespace BB6Coverage.Agent42Q4TailToS0Frame

open BB6Coverage
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8Q4Suffix
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48D0SweepLeftFacing

set_option maxHeartbeats 3000000

private theorem d0pow_length_local (k : Nat) :
    (d0pow k).length = 3*k := by
  induction k with
  | zero => simp [d0pow]
  | succ k ih => simp [d0pow,d0,ih] <;> omega

/-- The all-ones binary counter is the all-zero block word. -/
private theorem binDec_allOnes_local (k : Nat) :
    binDec k (2^k-1) = d0pow k := by
  induction k with
  | zero => simp [binDec,binaryCounterFuel,d0pow]
  | succ k ih =>
      have hp : 0 < 2^k := Nat.pow_pos (by decide)
      have hbound : 2^k-1 < 2^k := by omega
      have hpow : 2^(k+1)-1 = 2*(2^k-1)+1 := by
        rw [Nat.pow_succ]
        omega
      calc
        binDec (k+1) (2^(k+1)-1) =
            binDec (k+1) (2*(2^k-1)+1) := by rw [hpow]
        _ = d0 ++ binDec k (2^k-1) :=
            binDec_odd k (2^k-1) hbound
        _ = d0 ++ d0pow k := by rw [ih]
        _ = d0pow (k+1) := by rfl

private theorem config_ext_local (c d : Config)
    (hs : c.state = d.state)
    (hh : c.head = d.head)
    (ht : c.tape = d.tape) : c = d := by
  cases c
  cases d
  simp_all

/-- Left-facing tape after d0Sweep and q4Tail: the first n-1 blocks
are d0, and the remaining exterior is exactly the supplied residual. -/
private theorem q4Tail_left_stream
    (n : Nat) (ell : List Bool) (T : Int → Bool) (h : Int)
    (hn : 2 ≤ n) (hleft : T (h-1) = true)
    (hres : ∀ i : Nat, T (h-2-(i:Int)) = sideBit ell i) :
    ∀ i : Nat,
      (frameAt (d0Sweep n T h) (h+(3*n:Int))
        q4TailInside q4TailEnd).tape
        (h+(3*n:Int)-5-(i:Int)) =
      sideBit (d0pow (n-1) ++ ell) i := by
  let g : Int := h+(3*n:Int)
  let H : Int := g-5
  let U : Config := frameAt (d0Sweep n T h) g q4TailInside q4TailEnd
  have hprefixLen : (d0pow (n-1)).length = 3*(n-1) :=
    d0pow_length_local (n-1)
  intro i
  by_cases hi : i < 3*(n-1)
  · have hc := q4Tail_output_leftCounter n T h hn hleft i hi
    have happend :
        sideBit (d0pow (n-1) ++ ell) i = sideBit (d0pow (n-1)) i := by
      rw [Agent6Q4Prefix.sideBit_append_left (d0pow (n-1)) ell i
        (by rw [hprefixLen]; exact hi)]
    simpa [U,g,H] using hc.trans happend.symm
  · have hge : 3*(n-1) ≤ i := by omega
    let j : Nat := i-3*(n-1)
    let x : Int := H-(i:Int)
    have hcoord : x = h-2-(j:Int) := by
      dsimp [x,H,g,j]
      omega
    have hframe : U.tape x = d0Sweep n T h x := by
      change (frameAt (d0Sweep n T h) g q4TailInside q4TailEnd).tape x = _
      rw [frameAt_tape]
      have hlt : x-g < 0 := by dsimp [x,H,g]; omega
      have hnot : q4TailInside (x-g) = false := by
        simp [q4TailInside, not_le_of_gt hlt]
      simp [hnot]
    have hbefore : d0Sweep n T h x = T x := by
      apply d0Sweep_before
      dsimp [x,H,g]
      omega
    have htail : T x = sideBit ell j := by
      rw [hcoord]
      exact hres j
    have happend :
        sideBit (d0pow (n-1) ++ ell) i = sideBit ell j := by
      rw [Agent6Q4Prefix.sideBit_append_right (d0pow (n-1)) ell i
        (by rw [hprefixLen]; exact hge)]
      simp [j]
    calc
      U.tape (H-(i:Int)) = U.tape x := by rfl
      _ = d0Sweep n T h x := hframe
      _ = T x := hbefore
      _ = sideBit ell j := htail
      _ = sideBit (d0pow (n-1) ++ ell) i := happend.symm

/-- The q4Tail frame contributes the nine-cell S0 right word 011100111;
all cells beyond it are blank if the post-sweep right ray is blank. -/
private theorem q4Tail_right_stream
    (n : Nat) (T : Int → Bool) (h : Int)
    (hright : ∀ i : Nat,
      T (h+(3*n:Int)+5+(i:Int)) = false) :
    ∀ i : Nat,
      (frameAt (d0Sweep n T h) (h+(3*n:Int))
        q4TailInside q4TailEnd).tape
        (h+(3*n:Int)-5+1+(i:Int)) =
      sideBit (s0RightFacing 0) i := by
  let g : Int := h+(3*n:Int)
  let H : Int := g-5
  let U : Config := frameAt (d0Sweep n T h) g q4TailInside q4TailEnd
  intro i
  by_cases hi : i < 9
  · have hcases :
        i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨
        i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases hcases with h0|h1|h2|h3|h4|h5|h6|h7|h8
    all_goals
      have hcoord : H+1+(i:Int) = g+(-4+(i:Int)) := by
        dsimp [H,g]
        omega
      rw [hcoord]
      change (frameAt (d0Sweep n T h) g q4TailInside q4TailEnd).tape
        (g+(-4+(i:Int))) = _
      rw [frameAt_tape]
      simp_all [q4TailInside,q4TailEnd,s0RightFacing,d1pow,d1,sideBit]
  · let j : Nat := i-9
    have hcoord : H+1+(i:Int) = g+5+(j:Int) := by
      dsimp [H,g,j]
      omega
    rw [hcoord]
    have hframe : U.tape (g+5+(j:Int)) =
        d0Sweep n T h (g+5+(j:Int)) := by
      change (frameAt (d0Sweep n T h) g q4TailInside q4TailEnd).tape _ = _
      rw [frameAt_tape]
      have hgt : 4 < (g+5+(j:Int))-g := by omega
      have hnot : q4TailInside ((g+5+(j:Int))-g) = false := by
        simp [q4TailInside, not_le_of_gt hgt]
      simp [hnot]
    have hafter : d0Sweep n T h (g+5+(j:Int)) =
        T (g+5+(j:Int)) := by
      apply d0Sweep_after
      dsimp [g]
      omega
    have hblank : T (g+5+(j:Int)) = false := by
      simpa [g] using hright j
    have hlen : (s0RightFacing 0).length = 9 := by
      simp [s0RightFacing,d1pow,d1]
    have hbit : sideBit (s0RightFacing 0) i = false := by
      apply Agent6Q4Prefix.sideBit_ge_length
      rw [hlen]
      omega
    calc
      U.tape (g+5+(j:Int)) = d0Sweep n T h (g+5+(j:Int)) := hframe
      _ = T (g+5+(j:Int)) := hafter
      _ = false := hblank
      _ = sideBit (s0RightFacing 0) i := hbit.symm

/-- Exact generic conversion from a counted d1-block sweep followed by
q4Tail to the genuine S0 encoder configuration.  The source-specific
obligations are precisely the residual left ray and blank right ray. -/
theorem q4Tail_frame_eq_s0Config
    (n : Nat) (ell : List Bool) (T : Int → Bool) (h : Int)
    (hn : 2 ≤ n)
    (hleft : T (h-1) = true)
    (hres : ∀ i : Nat, T (h-2-(i:Int)) = sideBit ell i)
    (hright : ∀ i : Nat,
      T (h+(3*n:Int)+5+(i:Int)) = false) :
    frameAt (d0Sweep n T h) (h+(3*n:Int)) q4TailInside q4TailEnd =
      s0Config ell (n-1) (2^(n-1)-1) 0 (h+(3*n:Int)-5) := by
  let g : Int := h+(3*n:Int)
  let H : Int := g-5
  let U : Config := frameAt (d0Sweep n T h) g q4TailInside q4TailEnd
  have hleftStream : ∀ i : Nat,
      U.tape (H-(i:Int)) = sideBit (d0pow (n-1) ++ ell) i := by
    intro i
    simpa [U,H,g] using q4Tail_left_stream n ell T h hn hleft hres i
  have hrightStream : ∀ i : Nat,
      U.tape (H+1+(i:Int)) = sideBit (s0RightFacing 0) i := by
    intro i
    simpa [U,H,g] using q4Tail_right_stream n T h hright i
  have hface :
      s0LeftFacing ell (n-1) (2^(n-1)-1) = d0pow (n-1) ++ ell := by
    unfold s0LeftFacing
    rw [binDec_allOnes_local]
  apply config_ext_local
  · rfl
  · change (frameAt (d0Sweep n T h) g q4TailInside q4TailEnd).head = H
    rw [BB6Coverage.Agent6Q4Prefix.frameAt_head]
    dsimp [q4TailEnd,H,g]
    omega
  · funext x
    by_cases hx : x ≤ H
    · let i : Nat := Int.toNat (H-x)
      have hidx : (i:Int) = H-x := by
        dsimp [i]
        exact Int.toNat_of_nonneg (by omega)
      have hcoord : x = H-(i:Int) := by omega
      rw [hcoord]
      have hu := hleftStream i
      have hs := s0Config_left_cell ell (n-1) (2^(n-1)-1) 0 H i
      rw [hface] at hs
      exact hu.trans hs.symm
    · let i : Nat := Int.toNat (x-H-1)
      have hidx : (i:Int) = x-H-1 := by
        dsimp [i]
        exact Int.toNat_of_nonneg (by omega)
      have hcoord : x = H+1+(i:Int) := by omega
      rw [hcoord]
      have hu := hrightStream i
      have hs := s0Config_right_cell ell (n-1) (2^(n-1)-1) 0 H i
      exact hu.trans hs.symm

#print axioms q4Tail_frame_eq_s0Config

end BB6Coverage.Agent42Q4TailToS0Frame
