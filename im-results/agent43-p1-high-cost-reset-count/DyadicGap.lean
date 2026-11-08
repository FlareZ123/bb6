import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43TwoRun
private theorem pow8 (r : Nat) : 8^r = 2^(3*r) := by
  simpa only [show (8:Nat) = 2^3 by decide] using (Nat.pow_mul 2 3 r).symm

/-- Any positive remainder smaller than 2^n is at least the full 8^r block. -/
theorem dyadic_remainder
    (n r A K B : Nat)
    (hpos : 0 < B) (hsmall : B < 2^n)
    (heq : K*2^n = A*8^r+B) :
    3*r ≤ n ∧ 8^r ≤ B := by
  by_cases h : 3*r ≤ n
  · have hdiv : 8^r ∣ 2^n := by
      rw [pow8]
      exact Nat.pow_dvd_pow 2 h
    obtain ⟨q,hq⟩ := hdiv
    have hleft : 8^r ∣ K*2^n := by
      refine ⟨K*q, ?_⟩
      rw [hq]
      ac_rfl
    have hright : 8^r ∣ A*8^r := Nat.dvd_mul_left _ _
    have hd := Nat.dvd_sub hleft hright
    have hdiff : K*2^n - A*8^r = B := by omega
    rw [hdiff] at hd
    exact ⟨h, Nat.le_of_dvd hpos hd⟩
  · have hrev : n ≤ 3*r := by omega
    have hdiv : 2^n ∣ 8^r := by
      rw [pow8]
      exact Nat.pow_dvd_pow 2 hrev
    obtain ⟨q,hq⟩ := hdiv
    have hleft : 2^n ∣ K*2^n := Nat.dvd_mul_left _ _
    have hright : 2^n ∣ A*8^r := by
      refine ⟨A*q, ?_⟩
      rw [hq]
      ac_rfl
    have hd := Nat.dvd_sub hleft hright
    have hdiff : K*2^n - A*8^r = B := by omega
    rw [hdiff] at hd
    have hge := Nat.le_of_dvd hpos hd
    omega
end BB6.Agent43TwoRun

namespace BB6.Agent43TwoRun
private theorem square_doubling (n : Nat) (hn : 1 ≤ n) :
    (n+3)^2 ≤ 2*(n+2)^2 := by
  have hnn : n ≤ n*n := by
    simpa using (Nat.mul_le_mul_left n hn)
  simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
  omega

private theorem quadratic_lt_pow_A (n : Nat) (hn : 14 ≤ n) :
    10125*(n+2)^2 < 245*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hnbase : 14 ≤ n
    · have ih := ih hnbase
      have hgrowth := square_doubling n (by omega)
      have hscale := Nat.mul_le_mul_left 10125 hgrowth
      have hbound : 10125*(n+3)^2 ≤ 2*(10125*(n+2)^2) := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscale
      have hgoal : 10125*(n+3)^2 < 245*(2^n*2) := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.pow_succ] using hgoal
    · have heq : n = 13 := by omega
      subst n
      decide

private theorem quadratic_lt_pow_B (n : Nat) (hn : 15 ≤ n) :
    13851*(n+2)^2 < 147*2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hnbase : 15 ≤ n
    · have ih := ih hnbase
      have hgrowth := square_doubling n (by omega)
      have hscale := Nat.mul_le_mul_left 13851 hgrowth
      have hbound : 13851*(n+3)^2 ≤ 2*(13851*(n+2)^2) := by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscale
      have hgoal : 13851*(n+3)^2 < 147*(2^n*2) := by omega
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.pow_succ] using hgoal
    · have heq : n = 14 := by omega
      subst n
      decide

#print axioms BB6.Agent43TwoRun.quadratic_lt_pow_A
#print axioms BB6.Agent43TwoRun.quadratic_lt_pow_B
end BB6.Agent43TwoRun

namespace BB6.Agent43TwoRun
private theorem linear_lt_pow_A (n : Nat) (hn : 14 ≤ n) :
    35*n+90 < 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hbase : 14 ≤ n
    · have hprev := ih hbase
      have hgoal : 35*(n+1)+90 < 2^n*2 := by omega
      simpa [Nat.succ_eq_add_one, Nat.pow_succ] using hgoal
    · have heq : n = 13 := by omega
      subst n
      decide

private theorem linear_lt_pow_B (n : Nat) (hn : 14 ≤ n) :
    21*n+54 < 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hbase : 14 ≤ n
    · have hprev := ih hbase
      have hgoal : 21*(n+1)+54 < 2^n*2 := by omega
      simpa [Nat.succ_eq_add_one, Nat.pow_succ] using hgoal
    · have heq : n = 13 := by omega
      subst n
      decide

/-- The exact depth-two suffix equation after one depth-zero transition
from the critical blank-seed inverse hub has no natural solution. -/
theorem no_zero_then_twos
    (n r : Nat) (hn : 14 ≤ n)
    (heq : 245*2^n = (112*n+336*r+400)*8^r+(35*n+90)) : False := by
  have hsmall := linear_lt_pow_A n hn
  obtain ⟨hr, hpow⟩ :=
    dyadic_remainder n r (112*n+336*r+400) 245 (35*n+90)
      (by omega) hsmall heq
  have hA : (112*n+336*r+400)+1 ≤ 225*(n+2) := by omega
  have hB : 35*n+90 ≤ 45*(n+2) := by omega
  have hmul := Nat.mul_le_mul hA hB
  have hmul' : ((112*n+336*r+400)+1)*(35*n+90) ≤ 10125*(n+2)^2 := by
    calc
      _ ≤ (225*(n+2))*(45*(n+2)) := hmul
      _ = 10125*(n+2)^2 := by
        calc
          _ = (225*45)*((n+2)*(n+2)) := by ac_rfl
          _ = _ := by simp [Nat.pow_succ]
  have hsmallMul := Nat.mul_le_mul_left (112*n+336*r+400) hpow
  have h_expand :
      ((112*n+336*r+400)+1)*(35*n+90) =
        (112*n+336*r+400)*(35*n+90)+(35*n+90) := by
    simp [Nat.add_mul]
  have hineq : 245*2^n ≤ ((112*n+336*r+400)+1)*(35*n+90) := by
    omega
  have hnumeric := quadratic_lt_pow_A n hn
  omega

/-- The exact depth-two suffix equation after one depth-one transition
from the critical blank-seed inverse hub has no natural solution. -/
theorem no_one_then_twos
    (n r : Nat) (hn : 14 ≤ n)
    (heq : 147*2^n = (224*n+672*r+1024)*8^r+(21*n+54)) : False := by
  have hsmall := linear_lt_pow_B n hn
  obtain ⟨hr, hpow⟩ :=
    dyadic_remainder n r (224*n+672*r+1024) 147 (21*n+54)
      (by omega) hsmall heq
  by_cases hn15 : 15 ≤ n
  · have hA : (224*n+672*r+1024)+1 ≤ 513*(n+2) := by omega
    have hB : 21*n+54 ≤ 27*(n+2) := by omega
    have hmul := Nat.mul_le_mul hA hB
    have hmul' : ((224*n+672*r+1024)+1)*(21*n+54) ≤ 13851*(n+2)^2 := by
      calc
        _ ≤ (513*(n+2))*(27*(n+2)) := hmul
        _ = 13851*(n+2)^2 := by
          calc
            _ = (513*27)*((n+2)*(n+2)) := by ac_rfl
            _ = _ := by simp [Nat.pow_succ]
    have hsmallMul := Nat.mul_le_mul_left (224*n+672*r+1024) hpow
    have h_expand :
        ((224*n+672*r+1024)+1)*(21*n+54) =
          (224*n+672*r+1024)*(21*n+54)+(21*n+54) := by
      simp [Nat.add_mul]
    have hineq : 147*2^n ≤ ((224*n+672*r+1024)+1)*(21*n+54) := by
      omega
    have hnumeric := quadratic_lt_pow_B n hn15
    omega
  · have heq14 : n=14 := by omega
    subst n
    have hr2 : r≤2 := by
      by_cases h : r≤2
      · exact h
      · have hh : (8:Nat)^3≤8^r := Nat.pow_le_pow_right (by decide) (by omega)
        have h512 : 512≤8^r := by simpa using hh
        omega
    have hpow64 : 8^r≤64 := by
      have hh : 8^r≤(8:Nat)^2 := Nat.pow_le_pow_right (by decide) hr2
      simpa using hh
    have hA : 224*14+672*r+1024≤5504 := by omega
    have hmul := Nat.mul_le_mul hA hpow64
    have hbound : (224*14+672*r+1024)*8^r ≤5504*64 := hmul
    omega
end BB6.Agent43TwoRun