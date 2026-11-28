import ObstructionAlignment
import EqualHighMod384
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Exact all-F obstruction for the bounded inverse-residue sieve.

The generic density-one sieve is powerful on almost every terminal parameter, but
the authentic reset-to-High terminal families converge to the 2-adic point -3.
This module proves the precise obstruction: whenever D+3 is divisible by 4^n,
the length-n all-F inverse word has zero dyadic residue. Hence NoResidueWord n D
is false and that depth-n certificate cannot exclude the gate.
-/

namespace BB6.Agent2F321AllFarObstruction
open BB6.Agent31F321Density
open BB6.Agent2F321ObstructionAlignment
open BB6.Agent2F321Bulk
open BB6.Agent2F321EqualHigh
open BB6.Agent2F321EqualHighMod384

def farWord : Nat → List InverseLetter
  | 0 => []
  | n+1 => .far :: farWord n

theorem farWord_length (n : Nat) : (farWord n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [farWord, ih]

theorem compile_farWord_u (n : Nat) : (compile (farWord n)).u = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [farWord, compile, advance, ih]

theorem compile_farWord_shift (n : Nat) :
    (compile (farWord n)).shift = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [farWord, compile, advance, ih]
      omega

private theorem two_pow_even (n : Nat) :
    (2:Int)^(2*n) = (4:Int)^n := by
  calc
    (2:Int)^(2*n) = ((2:Int)^2)^n := Int.pow_mul
    _ = (4:Int)^n := by
      have h : (2:Int)^2 = 4 := by decide
      rw [h]

theorem compile_farWord_v (n : Nat) :
    (compile (farWord n)).v = 3 - 2*(4:Int)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [farWord, compile, advance]
      rw [ih, compile_farWord_shift, two_pow_even]
      have hp : (4:Int)^(n+1) = 4*(4:Int)^n := by
        rw [Int.pow_succ]
        ac_rfl
      rw [hp]
      omega

private theorem four_pow_eq_two_pow (n : Nat) :
    (4:Nat)^n = 2^(2*n) := by
  calc
    (4:Nat)^n = ((2:Nat)^2)^n := by
      have h : (2:Nat)^2 = 4 := by decide
      rw [h]
    _ = (2:Nat)^(2*n) := (Nat.pow_mul 2 2 n).symm

/-- The all-F word has exactly the expected zero residue in every dyadic
    neighbourhood of -3. -/
theorem farWord_residue_zero_of_nearMinusThree (n d : Nat)
    (h : NearMinusThree (2*n) d) :
    (((compile (farWord n)).u:Int)*(d:Int)+(compile (farWord n)).v) %
      ((2:Int)^(compile (farWord n)).shift) = 0 := by
  rcases h with ⟨q,hq⟩
  rw [compile_farWord_u, compile_farWord_v, compile_farWord_shift]
  have hpow : (4:Nat)^n = 2^(2*n) := four_pow_eq_two_pow n
  have hq4 : d+3 = 4^n*q := by simpa [hpow] using hq
  have hcast := congrArg (fun x:Nat => (x:Int)) hq4
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at hcast
  change (d:Int) + 3 = (4:Int)^n * (q:Int) at hcast
  rw [two_pow_even]
  have heq : (d:Int) + (3 - 2*(4:Int)^n) =
      (4:Int)^n * ((q:Int)-2) := by
    calc
      (d:Int) + (3 - 2*(4:Int)^n) =
          ((d:Int)+3) - 2*(4:Int)^n := by omega
      _ = (4:Int)^n*(q:Int) - 2*(4:Int)^n := by rw [hcast]
      _ = (4:Int)^n * ((q:Int)-2) := by
        rw [Int.mul_sub]
        omega
  have hone : ((1:Nat):Int) * (d:Int) = (d:Int) := by omega
  rw [hone]
  change ((d:Int) + (3 - 2*(4:Int)^n)) % (4:Int)^n = 0
  rw [heq]
  exact Int.mul_emod_right _ _

/-- Exact obstruction to the generic depth-n exclusion premise. -/
theorem nearMinusThree_blocks_NoResidueWord (n d : Nat)
    (h : NearMinusThree (2*n) d) :
    ¬ NoResidueWord n d := by
  intro hn
  have hno := hn (farWord n) (farWord_length n)
  exact hno (farWord_residue_zero_of_nearMinusThree n d h)

/-- Every sufficiently long authentic M1 reset-to-terminal High tail defeats
    the generic bounded-depth residue premise via its all-F word. -/
theorem middleOdd_tail_blocks_depth
    {time k a d A D depth : Nat}
    (hr : CounterReach 1 1 time a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 1)
    (hh : HighRun k (4*a+6) 1 A D)
    (ht : A = D + 1)
    (hdepth : 2*depth ≤ k+2) :
    ¬ NoResidueWord depth D := by
  apply nearMinusThree_blocks_NoResidueWord depth D
  exact middleOdd_terminal_nearMinusThree
    hr h1 h2 hp hh ht hdepth

/-- Every sufficiently long authentic M2 reset-to-terminal High tail has the
    same exact obstruction. -/
theorem middleEven_tail_blocks_depth
    {k a A D depth : Nat}
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1)
    (hdepth : 2*depth ≤ k) :
    ¬ NoResidueWord depth D := by
  apply nearMinusThree_blocks_NoResidueWord depth D
  exact middleEven_terminal_nearMinusThree hh ht hdepth

private theorem pow_factor_of_le {N e : Nat} (h : N ≤ e) :
    ∃ q : Nat, 2^e = 2^N * q := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le h
  subst e
  refine ⟨2^r, ?_⟩
  exact Nat.pow_add 2 N r

private theorem four_times_pow (k : Nat) :
    4 * 2^k = 2^(k+2) := by
  calc
    4 * 2^k = 2^2 * 2^k := by
      have h2 : 2^2 = 4 := by decide
      rw [h2]
    _ = 2^(2+k) := (Nat.pow_add 2 2 k).symm
    _ = 2^(k+2) := by congr 1 <;> omega

/-- Equal-reset terminal tails have the same exceptional 2-adic limit.
The root phase theorem additionally restricts their High length to 12 or 18
modulo 24. -/
theorem equalHigh_terminal_nearMinusThree
    {k a A D N : Nat}
    (hh : HighRun k (2*a+4) 1 A D)
    (ht : A = D + 1)
    (hN : N ≤ k+2) : NearMinusThree N D := by
  have hterm := equal_high_terminal_parameter hh ht
  rcases pow_factor_of_le hN with ⟨q,hq⟩
  refine ⟨q, ?_⟩
  rw [hterm, four_times_pow k]
  exact hq

/-- The third authentic small-second anchor family, Equal followed by High,
also defeats every fixed-depth terminal-only residue sieve on sufficiently
long tails. Its root-reachable predecessor forces k mod 24 in {12,18}. -/
theorem equalHigh_tail_blocks_depth
    {n k a A D depth : Nat}
    (hn : 0 < n)
    (hr : CounterReach 1 1 n a a)
    (hh : HighRun k (2*a+4) 1 A D)
    (ht : A = D + 1)
    (hdepth : 2*depth ≤ k+2) :
    (k % 24 = 12 ∨ k % 24 = 18) ∧
      k % 768 ∈ equalHighAllowedK768 ∧
      ¬ NoResidueWord depth D := by
  have hphase := equal_high_terminal_length_mod24 hn hr hh ht
  have hk := equalHigh_root_k_mod768 hn hr hh ht
  constructor
  · exact hphase
  constructor
  · exact hk
  · apply nearMinusThree_blocks_NoResidueWord
    exact equalHigh_terminal_nearMinusThree hh ht hdepth

#print axioms equalHigh_terminal_nearMinusThree
#print axioms equalHigh_tail_blocks_depth

#print axioms nearMinusThree_blocks_NoResidueWord
#print axioms middleOdd_tail_blocks_depth
#print axioms middleEven_tail_blocks_depth
end BB6.Agent2F321AllFarObstruction
