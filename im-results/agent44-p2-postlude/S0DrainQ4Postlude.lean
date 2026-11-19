import S0CountedDrain
import Q4S0FirstCycleMacros
import Lean.Elab.Tactic.Omega

/-!
# Generic S0 all-ones drain followed by the q4/S0 postlude

The P2 q4-tail residual is not a run of m+8 ones followed by four
zeroes.  Its corrected prefix is 1^(m+2) ++ 0100.  After the all-ones
S0 drain, the existing q4S0Postlude_at applies with
K = 3*a + (m+2).  This file isolates that reusable source composition.
The separate P2 q4Tail-to-s0Config tape identity is not proved here.
-/

namespace BB6Coverage.Agent44P2Postlude

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent42Q4S0Drain
open BB6Coverage.Agent48Q4S0Macros
open BB6Coverage.Agent48Champion

set_option maxHeartbeats 4000000

private theorem sideBit_replicate_true_local (n i : Nat) (hi : i<n) :
    sideBit (List.replicate n true) i = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [sideBit]
      | succ i =>
          have hi' : i<n := by omega
          simpa [sideBit] using ih i hi'


/-- The exact residual context required by the corrected P2 postlude. -/
def p2ResidualLeft (m : Nat) (tail : List Bool) : List Bool :=
  List.replicate (m+2) true ++ [false,true,false,false] ++ tail

/-- A generic all-ones S0 drain followed by the existing q4/S0 postlude.
The only residual-context hypotheses are the leading one-run and the
four-bit 0100 boundary, in head-facing order. -/
theorem s0Config_allOnesDrain_q4Postlude
    (ell : List Bool) (a m : Nat) (H : Int)
    (hprefix : ∀ i : Nat, i < m → sideBit ell i = true)
    (h0 : sideBit ell m = false)
    (h1 : sideBit ell (m+1) = true)
    (h2 : sideBit ell (m+2) = false)
    (h3 : sideBit ell (m+3) = false) :
    run tm2
      ((6*4^a + 42*2^a - 12*a - 48) + (3*(3*a+m)+4))
      (s0Config ell a (2^a-1) 0 H) =
    some (q4FrameAt
      (s0LeftSweep (3*a+m)
        (s0Config ell a 0 (2^a-1) H).tape H)
      (H-(3*a+m)) q4S0Final4Inside q4S0Final4End) := by
  let K := 3*a+m
  let T := (s0Config ell a 0 (2^a-1) H).tape
  have hpow : 0 < 2^a := Nat.pow_pos (by decide)
  have hbound : 2^a-1 < 2^a :=
    Nat.sub_lt hpow (by decide)
  have hD := s0Config_counted_drain_closed ell a a H hbound
  have hleft : s0LeftFacing ell a 0 = d1pow a ++ ell := by
    simp [s0LeftFacing, binDec_zero]
  have hones : s0LeftOnes T H K := by
    intro i hi
    have hcell := s0Config_left_cell ell a 0 (2^a-1) H i
    change T (H-(i:Int)) = sideBit (s0LeftFacing ell a 0) i at hcell
    rw [hleft] at hcell
    by_cases hia : i < 3*a
    · rw [Agent6Q4Prefix.sideBit_append_left (d1pow a) ell i (by
        rw [d1pow_length]
        exact hia)] at hcell
      exact hcell.trans
        (Agent6Q4Prefix.sideBit_d1pow_true a i hia)
    · have hj : i-3*a < m := by omega
      rw [Agent6Q4Prefix.sideBit_append_right (d1pow a) ell i (by
        rw [d1pow_length]
        omega)] at hcell
      have hidx : i-3*a < m := hj
      rw [d1pow_length] at hcell
      exact hcell.trans (hprefix (i-3*a) hidx)
  have hright : T (H+1) = false := by
    have hcell := s0Config_right_cell ell a 0 (2^a-1) H 0
    simpa [T, s0RightFacing, sideBit] using hcell
  let h' : Int := H-(K:Int)
  have hsweep (x : Int) (hx : x ≤ h') :
      s0LeftSweep K T H x = T x := by
    rw [s0LeftSweep_shift]
    simp [h', K, hx]
  have hcell (j : Nat) :
      T (h'-(j:Int)) = sideBit ell (m+j) := by
    have hc := s0Config_left_cell ell a 0 (2^a-1) H (3*a+m+j)
    change T (H-(3*a+m+j:Int)) =
      sideBit (s0LeftFacing ell a 0) (3*a+m+j) at hc
    rw [hleft] at hc
    rw [Agent6Q4Prefix.sideBit_append_right (d1pow a) ell
      (3*a+m+j) (by rw [d1pow_length]; omega)] at hc
    rw [d1pow_length] at hc
    have hidx : 3*a+m+j-3*a = m+j := by omega
    have hcoord : H-(3*a+m+j:Int) = h'-(j:Int) := by
      dsimp [h', K]
      omega
    rw [hcoord] at hc
    simpa [hidx] using hc
  have hguard :
      q4S0Final4Input (s0LeftSweep K T H) h' := by
    refine ⟨?_,?_,?_,?_⟩
    · rw [hsweep (h'-3) (by omega)]
      simpa using (hcell 3).trans h3
    · rw [hsweep (h'-2) (by omega)]
      simpa using (hcell 2).trans h2
    · rw [hsweep (h'-1) (by omega)]
      simpa using (hcell 1).trans h1
    · rw [hsweep h' (by omega)]
      simpa using (hcell 0).trans h0
  have hQ := q4S0Postlude_at K T H hones hright hguard
  have hQ' :
      run tm2 (3*K+4) (s0Config ell a 0 (2^a-1) H) =
        some (q4FrameAt (s0LeftSweep K T H) h'
          q4S0Final4Inside q4S0Final4End) := by
    simpa [T, K, h'] using hQ
  calc
    run tm2
        ((6*4^a + 42*2^a - 12*a - 48) + (3*(3*a+m)+4))
        (s0Config ell a (2^a-1) 0 H)
      = (run tm2 (6*4^a + 42*2^a - 12*a - 48)
          (s0Config ell a (2^a-1) 0 H)).bind
          (fun c => run tm2 (3*K+4) c) := by
            rw [run_append]
            simp [K]
    _ = some (q4FrameAt (s0LeftSweep K T H) h'
          q4S0Final4Inside q4S0Final4End) := by
            rw [hD]
            simp only [Option.bind_some]
            exact hQ'

/-- The corrected P2 S0 postlude: after the P2 prefix has produced the
natural S0 input with width a=n-1 and residual 1^(m+2) ++ 0100 ++ tail,
the counted drain and q4/S0 postlude return to state 4 at head 1. -/
theorem p2S0Drain_q4Postlude
    (m n : Nat) (tail : List Bool) (hn : 1 ≤ n) :
    let a := n-1
    let H : Nat := (m+2+3*n)
    let K := 3*(n-1)+(m+2)
    run tm2
      ((6*4^(n-1) + 42*2^(n-1) - 12*(n-1) - 48) + (3*H-5))
      (s0Config (p2ResidualLeft m tail) (n-1)
        (2^(n-1)-1) 0 (H:Int)) =
    some (q4FrameAt
      (s0LeftSweep K
        (s0Config (p2ResidualLeft m tail) (n-1)
          0 (2^(n-1)-1) (H:Int)).tape (H:Int))
      3 q4S0Final4Inside q4S0Final4End) := by
  dsimp
  let a := n-1
  let H : Nat := (m+2+3*n)
  let K := 3*a+(m+2)
  have hprefix : ∀ i : Nat, i<m+2 →
      sideBit (p2ResidualLeft m tail) i = true := by
    intro i hi
    rw [Agent6Q4Prefix.sideBit_append_left
      (List.replicate (m+2) true)
      ([false,true,false,false] ++ tail) i (by simp)]
    exact sideBit_replicate_true_local (m+2) i hi
  have h0 : sideBit (p2ResidualLeft m tail) (m+2) = false := by
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (m+2) true)
      ([false,true,false,false] ++ tail) (m+2) (by simp)]
    simp [sideBit]
  have h1 : sideBit (p2ResidualLeft m tail) (m+3) = true := by
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (m+2) true)
      ([false,true,false,false] ++ tail) (m+3) (by simp)]
    simp [sideBit]
  have h2 : sideBit (p2ResidualLeft m tail) (m+4) = false := by
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (m+2) true)
      ([false,true,false,false] ++ tail) (m+4) (by simp)]
    simp [sideBit]
  have h3 : sideBit (p2ResidualLeft m tail) (m+5) = false := by
    rw [Agent6Q4Prefix.sideBit_append_right
      (List.replicate (m+2) true)
      ([false,true,false,false] ++ tail) (m+5) (by simp)]
    simp [sideBit]
  have hcenter : (H:Int)-(K:Int)=3 := by
    dsimp [H,K,a]
    omega
  have hcost : 3*K+4 = 3*H-5 := by
    dsimp [H,K,a]
    omega
  have hrun := s0Config_allOnesDrain_q4Postlude
    (p2ResidualLeft m tail) a (m+2) (H:Int) hprefix h0 h1 h2 h3
  rw [hcost] at hrun
  simpa [a,H,K,hcenter] using hrun

#print axioms s0Config_allOnesDrain_q4Postlude
#print axioms p2S0Drain_q4Postlude

end BB6Coverage.Agent44P2Postlude
