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
    (t m k : Nat) (_ht : 0 < t) (hm : 0 < m) (hmOdd : m % 2 = 1)
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
    have hP : 1 ≤ 5^t*m := by
      have hp : 0 < 5^t*m :=
        Nat.mul_pos (Nat.pow_pos (by decide)) hm
      omega
    rw [← hq] at hfactor
    have hshift : (5^t*m-1)+2 = 5^t*m+1 := by omega
    rw [hshift] at hfactor
    exact hfactor.symm
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
private theorem odd_block_exit_terminal_mod_five_eq
    (t m k v : Nat) (ht : 0 < t)
    (hidentity :
      2^(k+v+2) + 5*2^v =
        5^t*m*(2^(v+1)+3) + 2^v*(2*v+4) + 3) :
    2^(k+v+2) % 5 = (2^v*(2*v+4)+3) % 5 := by
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
  have hAB :
      (5^t*m*(2^(v+1)+3) + 2^v*(2*v+4)) % 5 =
        (2^v*(2*v+4)) % 5 := by
    calc
      _ = ((5^t*m*(2^(v+1)+3)) % 5 +
            (2^v*(2*v+4)) % 5) % 5 := Nat.add_mod _ _ _
      _ = (0 + (2^v*(2*v+4)) % 5) % 5 := by rw [hprod]
      _ = (2^v*(2*v+4)) % 5 := by simp
  have hright :
      (5^t*m*(2^(v+1)+3)+2^v*(2*v+4)+3) % 5 =
        (2^v*(2*v+4)+3) % 5 := by
    calc
      _ = ((5^t*m*(2^(v+1)+3) + 2^v*(2*v+4)) % 5 + 3 % 5) % 5 :=
        Nat.add_mod _ _ _
      _ = ((2^v*(2*v+4)) % 5 + 3 % 5) % 5 := by rw [hAB]
      _ = (2^v*(2*v+4)+3) % 5 := (Nat.add_mod _ _ _).symm
  have h := congrArg (fun z : Nat => z % 5) hidentity
  rw [hleft, hright] at h
  exact h

private theorem pow_two_mod_five_period_four (n : Nat) :
    2^n % 5 = 2^(n % 4) % 5 := by
  have hperiod : ∀ j : Nat, (2:Nat)^(4*j) % 5 = 1 := by
    intro j
    induction j with
    | zero => norm_num
    | succ j ih =>
      have hexp : 4*(j+1) = 4*j+4 := by omega
      rw [hexp, Nat.pow_add]
      have hmul :
          (2^(4*j)*2^4) % 5 =
            ((2^(4*j) % 5)*(2^4 % 5)) % 5 := Nat.mul_mod _ _ _
      rw [hmul, ih]
      norm_num
  have hdecomp : n = 4*(n/4)+n%4 := by omega
  rw [hdecomp, Nat.pow_add]
  have hmul :
      (2^(4*(n/4))*2^(n%4)) % 5 =
        ((2^(4*(n/4)) % 5)*(2^(n%4) % 5)) % 5 := Nat.mul_mod _ _ _
  rw [hmul, hperiod]
  simp

private theorem terminal_mod20_table (k v : Nat)
    (h : 2^(k+v+2) % 5 = (2^v*(2*v+4)+3) % 5) :
    (k%4=0 ∧ (v%20=7 ∨ v%20=13 ∨ v%20=14 ∨ v%20=16)) ∨
    (k%4=1 ∧ (v%20=5 ∨ v%20=6 ∨ v%20=8 ∨ v%20=19)) ∨
    (k%4=2 ∧ (v%20=3 ∨ v%20=9 ∨ v%20=10 ∨ v%20=12)) ∨
    (k%4=3 ∧ (v%20=0 ∨ v%20=11 ∨ v%20=17 ∨ v%20=18)) := by
  have hv4 : v%4 = (v%20)%4 := by omega
  have hv5 : v%5 = (v%20)%5 := by omega
  have hexp :
      (k+v+2)%4 = ((k%4)+(v%20)%4+2)%4 := by
    rw [← hv4]
    omega
  have hpowLeft :
      2^(k+v+2) % 5 =
        2^(((k%4)+(v%20)%4+2)%4) % 5 := by
    rw [pow_two_mod_five_period_four, hexp]
  have hpowRight :
      2^v % 5 = 2^((v%20)%4) % 5 := by
    rw [pow_two_mod_five_period_four, hv4]
  have hlinear :
      (2*v+4) % 5 = (2*((v%20)%5)+4) % 5 := by omega
  have h' :
      2^(((k%4)+(v%20)%4+2)%4) % 5 =
        ((2^((v%20)%4) % 5) *
          ((2*((v%20)%5)+4) % 5) + 3) % 5 := by
    calc
      _ = 2^(k+v+2) % 5 := hpowLeft.symm
      _ = (2^v*(2*v+4)+3) % 5 := h
      _ = ((2^v % 5)*((2*v+4) % 5)+3) % 5 := by
        simp [Nat.mul_mod, Nat.add_mod]
      _ = ((2^((v%20)%4) % 5) *
            ((2*((v%20)%5)+4) % 5) + 3) % 5 := by
        rw [hpowRight, hlinear]
  have hklt : k%4 < 4 := Nat.mod_lt _ (by decide)
  have hvlt : v%20 < 20 := Nat.mod_lt _ (by decide)
  interval_cases hk : k%4 <;> interval_cases hv : v%20 <;>
    norm_num [hk, hv] at h' <;> norm_num [hk, hv]

theorem odd_block_exit_terminal_nonzero_mod_five
    (t m k : Nat) (ht : 0 < t) (hm : 0 < m) (hmOdd : m % 2 = 1)
    (hterm :
      highLevelNext (.N (5^t*m-1)) = some (.N (haltTower k))) :
    ∃ q v,
      5^t*m-1 = oddTower q v ∧
      runHigh t (some (.N (2^t*m-1))) = some (.N (5^t*m-1)) ∧
      (5^t*m-1) % 2 = 0 ∧
      ¬ 5 ∣ (2^v*(2*v+4)+3) := by
  rcases odd_block_exit_terminal_identity t m k ht hm hmOdd hterm with
    ⟨q, v, hq, hblock, hExitEven, hidentity⟩
  have hpowNonzero : 2^(k+v+2) % 5 ≠ 0 := by
    rcases pow_two_mod5_cases (k+v+2) with h1 | h2 | h4 | h3 <;> omega
  have hmod := odd_block_exit_terminal_mod_five_eq t m k v ht hidentity
  have hnonzero : ¬ 5 ∣ 2^v*(2*v+4)+3 := by
    intro hdiv
    have hzero : (2^v*(2*v+4)+3) % 5 = 0 :=
      Nat.dvd_iff_mod_eq_zero.mp hdiv
    have hpowZero : 2^(k+v+2) % 5 = 0 := by
      simpa [hzero] using hmod
    exact hpowNonzero hpowZero
  exact ⟨q, v, hq, hblock, hExitEven, hnonzero⟩

/-- The terminal exponent modulo four selects exactly four possible
valuation classes modulo twenty for an odd-block exit. -/
theorem odd_block_exit_terminal_mod20
    (t m k : Nat) (ht : 0 < t) (hm : 0 < m) (hmOdd : m % 2 = 1)
    (hterm :
      highLevelNext (.N (5^t*m-1)) = some (.N (haltTower k))) :
    ∃ q v,
      5^t*m-1 = oddTower q v ∧
      runHigh t (some (.N (2^t*m-1))) = some (.N (5^t*m-1)) ∧
      (5^t*m-1) % 2 = 0 ∧
      ((k%4=0 ∧ (v%20=7 ∨ v%20=13 ∨ v%20=14 ∨ v%20=16)) ∨
       (k%4=1 ∧ (v%20=5 ∨ v%20=6 ∨ v%20=8 ∨ v%20=19)) ∨
       (k%4=2 ∧ (v%20=3 ∨ v%20=9 ∨ v%20=10 ∨ v%20=12)) ∨
       (k%4=3 ∧ (v%20=0 ∨ v%20=11 ∨ v%20=17 ∨ v%20=18))) := by
  rcases odd_block_exit_terminal_identity t m k ht hm hmOdd hterm with
    ⟨q, v, hq, hblock, hExitEven, hidentity⟩
  have hmod := odd_block_exit_terminal_mod_five_eq t m k v ht hidentity
  have htable := terminal_mod20_table k v hmod
  exact ⟨q, v, hq, hblock, hExitEven, htable⟩

#print axioms BB6.Agent20.NeedleOddBlockExit.odd_block_exit_terminal_mod20

end BB6.Agent20.NeedleOddBlockExit

#print axioms BB6.Agent20.NeedleOddBlockExit.odd_block_exit_terminal_identity
#print axioms BB6.Agent20.NeedleOddBlockExit.odd_block_exit_terminal_nonzero_mod_five
#print axioms BB6.Agent20.NeedleOddBlockExit.odd_block_exit_terminal_mod20
