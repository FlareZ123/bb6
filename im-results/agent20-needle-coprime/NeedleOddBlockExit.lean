import SpaceNeedleOddBlocksSource
import Mathlib

set_option maxHeartbeats 0

namespace BB6.Agent20.NeedleOddBlockExit

open BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/--
A nonempty maximal odd block with odd parameter m exits at the even
counter 5^t*m-1. If that exit feeds a terminal tower in one further
high-level transition, the terminal exponent and exit valuation satisfy
this exact identity.

The trajectory premise is source-valid: odd_block supplies the t-step
run from 2^t*m-1 to 5^t*m-1, and highLevelNext is the original pinned
machine's successor.
-/
theorem odd_block_exit_terminal_identity
    (t m k : Nat) (ht : 0 < t) (hm : 0 < m) (hmOdd : m % 2 = 1)
    (hterm :
      highLevelNext (.N (5^t*m-1)) = some (.N (haltTower k))) :
    ∃ q v,
      5^t*m-1 = oddTower q v ∧
      runHigh t (some (.N (2^t*m-1))) = some (.N (5^t*m-1)) ∧
      (5^t*m-1) % 2 = 0 ∧
      2^(k+v+2) + 5*2^v =
        5^t*m*(2^(v+1)+3) + 2^v*(2*v+4) + 3 := by
  have hblock := odd_block t m hm
  have hExitEven := odd_block_exits_even t m hmOdd
  rcases
      (highLevelNext_iff_oddTower (5^t*m-1) (haltTower k)).mp hterm with
    ⟨q, v, hq, _⟩
  have hsource : 2^v*(2*q+3) = 5^t*m+1 := by
    have hfactor := oddTower_factor q v
    rw [← hq] at hfactor
    omega
  have hfeed :
      2^(k+2)+3 = (2^(v+1)+3)*(2*q+3)+2*v :=
    (predecessor_power_identity q v k).mp (by simpa [hq] using hterm)
  have hpow : 2^(k+v+2) = 2^(k+2)*2^v := by
    rw [show k+v+2 = (k+2)+v by omega, Nat.pow_add]
  have hpowv : 2^(v+1) = 2*2^v := by
    rw [Nat.pow_succ']
  have hmul :
      2^(k+v+2)+3*2^v =
        (2^(v+1)+3)*(2^v*(2*q+3))+2^(v+1)*v := by
    calc
      _ = (2^(k+2)+3)*2^v := by rw [hpow, Nat.add_mul]
      _ = ((2^(v+1)+3)*(2*q+3)+2*v)*2^v := by rw [hfeed]
      _ = (2^(v+1)+3)*(2^v*(2*q+3))+2^(v+1)*v := by
        rw [hpowv]
        ring
  have hmul' :
      2^(k+v+2)+3*2^v =
        (2^(v+1)+3)*(5^t*m+1)+2^(v+1)*v := by
    simpa [hsource] using hmul
  have hfinal :
      2^(k+v+2)+5*2^v =
        5^t*m*(2^(v+1)+3)+2^v*(2*v+4)+3 := by
    nlinarith [hmul', hpowv]
  exact ⟨q, v, hq, hblock, hExitEven, hfinal⟩

/--
The odd-block-exit terminal identity forces the valuation-dependent
right-hand residue to be a unit modulo five.
-/
theorem odd_block_exit_terminal_nonzero_mod_five
    (t m k : Nat) (ht : 0 < t) (hm : 0 < m) (hmOdd : m % 2 = 1)
    (hterm :
      highLevelNext (.N (5^t*m-1)) = some (.N (haltTower k))) :
    ∃ q v,
      5^t*m-1 = oddTower q v ∧
      runHigh t (some (.N (2^t*m-1))) = some (.N (5^t*m-1)) ∧
      (5^t*m-1) % 2 = 0 ∧
      5 ∤ (2^v*(2*v+4)+3) := by
  rcases odd_block_exit_terminal_identity t m k ht hm hmOdd hterm with
    ⟨q, v, hq, hblock, hExitEven, hidentity⟩
  have hpowNonzero : 2^(k+v+2) % 5 ≠ 0 := by
    rcases pow_two_mod5_cases (k+v+2) with h1 | h2 | h4 | h3 <;> omega
  have hpowT : 5^t % 5 = 0 := by
    cases t with
    | zero => omega
    | succ t => simp [Nat.pow_succ']
  have hprod :
      (5^t*m*(2^(v+1)+3)) % 5 = 0 := by
    simp [Nat.mul_mod, hpowT]
  have hleft :
      (2^(k+v+2)+5*2^v) % 5 = 2^(k+v+2) % 5 := by
    rw [Nat.add_mod]
    simp
  have hright :
      (5^t*m*(2^(v+1)+3)+(2^v*(2*v+4)+3)) % 5 =
        (2^v*(2*v+4)+3) % 5 := by
    rw [Nat.add_mod, hprod]
    simp
  have hmod :
      2^(k+v+2) % 5 = (2^v*(2*v+4)+3) % 5 := by
    have h := congrArg (fun z : Nat => z % 5) hidentity
    rw [hleft, hright] at h
    exact h
  have hnonzero : 5 ∤ 2^v*(2*v+4)+3 := by
    intro hdiv
    have hzero : (2^v*(2*v+4)+3) % 5 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hdiv
    have hpowZero : 2^(k+v+2) % 5 = 0 := by
      simpa [hzero] using hmod
    exact hpowNonzero hpowZero
  exact ⟨q, v, hq, hblock, hExitEven, hnonzero⟩

end BB6.Agent20.NeedleOddBlockExit

#print axioms BB6.Agent20.NeedleOddBlockExit.odd_block_exit_terminal_identity
#print axioms BB6.Agent20.NeedleOddBlockExit.odd_block_exit_terminal_nonzero_mod_five
