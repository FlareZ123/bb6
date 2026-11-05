import OneResetTwoAdic

set_option maxHeartbeats 2000000
namespace BB6.Agent50TwoReset
private theorem sharp_sextic_step (x : Nat) (hx : 44 ≤ x) :
    576*(x+1)^6 ≤ 2*(576*x^6) := by
  have hlin : 44*(x+1) ≤ 45*x := by omega
  have hpow := Nat.pow_le_pow_left hlin 6
  have hratio : 45^6 ≤ 2*44^6 := by decide
  have hscaled : 44^6*(576*(x+1)^6) ≤
      45^6*(576*x^6) := by
    calc
      _ = 576*(44*(x+1))^6 := by simp only [Nat.mul_pow]; ac_rfl
      _ ≤ 576*(45*x)^6 := Nat.mul_le_mul_left 576 hpow
      _ = 45^6*(576*x^6) := by simp only [Nat.mul_pow]; ac_rfl
  have hscaled2 : 45^6*(576*x^6) ≤
      (2*44^6)*(576*x^6) :=
    Nat.mul_le_mul_right _ hratio
  have hscaled3 : 44^6*(576*(x+1)^6) ≤
      44^6*(2*(576*x^6)) := by
    calc
      _ ≤ 45^6*(576*x^6) := hscaled
      _ ≤ (2*44^6)*(576*x^6) := hscaled2
      _ = _ := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hscaled3 (by decide)

theorem sharp_sextic_growth (n : Nat) (hn : 42 ≤ n) :
    576*(n+2)^6 < 2^n := by
  have h : ∀ k : Nat, 576*(k+44)^6 < 2^(k+42) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hs := sharp_sextic_step (k+44) (by omega)
      have hp : 2*(576*(k+44)^6) < 2*(2^(k+42)) :=
        Nat.mul_lt_mul_of_pos_left ih (by decide)
      have ht : 576*((k+44)+1)^6 < 2*2^(k+42) :=
        Nat.lt_of_le_of_lt hs hp
      calc
        576*((k+1)+44)^6 = 576*((k+44)+1)^6 := by
          rw [show (k+1)+44=(k+44)+1 by omega]
        _ < 2*2^(k+42) := ht
        _ = 2^((k+1)+42) := by
          calc
            _ = 2^(k+42)*2 := Nat.mul_comm 2 (2^(k+42))
            _ = 2^((k+42)+1) := (Nat.pow_succ 2 (k+42)).symm
            _ = 2^((k+1)+42) :=
              congrArg (fun e : Nat => 2^e) (by omega)
  simpa only [show (n-42)+44=n+2 by omega,
    show (n-42)+42=n by omega] using h (n-42)

theorem two_reset_sharp_budget
    (n m l s M N D F V C : Nat)
    (hn : 42 ≤ n)
    (hfirst : 2^m ≤ 24*(n+2)^3)
    (hMpos : 0<M) (hMbound : M≤4*(n+2))
    (hNpos : 0<N) (hNbound : N≤6*(n+2))
    (hreset : 2^l*D+M=(7*V)*2^(n-m))
    (hsuffix : 2^s*F+N=(7*C)*2^(n-m-l)) :
    2^(m+l+s) ≤ 576*(n+2)^5 := by
  let x := n+2
  have hsextic : 576*x^6 < 2^n := by simpa only [x] using sharp_sextic_growth n hn
  have hxpos : 0<x := by dsimp [x]; omega
  have hxpow4 : x^4 ≤ x^6 := Nat.pow_le_pow_right hxpos (by decide)
  have hxpow5 : x^5 ≤ x^6 := Nat.pow_le_pow_right hxpos (by decide)
  have hP4 : 96*x^4 < 2^n := by
    have hle : 96*x^4 ≤ 576*x^6 := by
      have hmul := Nat.mul_le_mul_left 96 hxpow4
      omega
    omega
  have hP5 : 576*x^5 < 2^n := by
    have hmul := Nat.mul_le_mul_left 576 hxpow5
    omega
  have hfirst' : 2^m ≤ 24*x^3 := hfirst
  have hm : m<n := by
    by_cases h : m<n
    · exact h
    have hh : n≤m := by omega
    have hp : 2^n ≤ 2^m := Nat.pow_le_pow_right (by decide) hh
    have hx3 : x^3 ≤ x^6 := Nat.pow_le_pow_right hxpos (by decide)
    have hsmall : 24*x^3 < 2^n := by
      have hd : 24*x^3 ≤ 576*x^6 := by
        have hh := Nat.mul_le_mul_left 24 hx3
        omega
      omega
    omega
  have hpowm : 2^n = 2^m*2^(n-m) := by
    calc
      2^n = 2^(m+(n-m)) := congrArg (fun e:Nat => 2^e) (by omega)
      _ = 2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
  have hMprod : 2^m*M ≤ 96*x^4 := by
    calc
      _ ≤ (24*x^3)*(4*x) := Nat.mul_le_mul hfirst' (by simpa only [x] using hMbound)
      _ = 96*x^4 := by simp only [Nat.pow_succ, Nat.pow_zero]; ac_rfl
  have hMsmall : M < 2^(n-m) := by
    have hlt : 2^m*M < 2^m*2^(n-m) := by rw [←hpowm]; omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hdiv := BB6.Agent28.power_remainder_division (n-m) l (7*V) D M
      hMpos hMsmall hreset
  have hLbound : 2^l ≤4*x := by omega
  have hl : l<n-m := by
    have hsm : 2^l < 2^(n-m) := by omega
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<(2:Nat))).mp hsm
  have hpowml : 2^n = (2^m*2^l)*2^(n-m-l) := by
    calc
      2^n = 2^((m+l)+(n-m-l)) := congrArg (fun e:Nat => 2^e) (by omega)
      _ = (2^m*2^l)*2^(n-m-l) := by rw [Nat.pow_add,Nat.pow_add]
  have hNprod : (2^m*2^l)*N ≤576*x^5 := by
    calc
      _ ≤ ((24*x^3)*(4*x))*(6*x) :=
         Nat.mul_le_mul (Nat.mul_le_mul hfirst' hLbound) (by simpa only [x] using hNbound)
      _ = 576*x^5 := by simp only [Nat.pow_succ, Nat.pow_zero]; ac_rfl
  have hNsmall : N <2^(n-m-l) := by
    have hlt : (2^m*2^l)*N < (2^m*2^l)*2^(n-m-l) := by rw [←hpowml]; omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hdiv2 := BB6.Agent28.power_remainder_division (n-m-l) s (7*C) F N
      hNpos hNsmall hsuffix
  have hSbound : 2^s ≤6*x := by omega
  calc
    2^(m+l+s) = (2^m*2^l)*2^s := by simp only [Nat.pow_add]
    _ ≤ (24*x^3* (4*x))*(6*x) :=
       Nat.mul_le_mul (Nat.mul_le_mul hfirst' hLbound) hSbound
    _ = 576*(n+2)^5 := by
      have hc : (24:Nat)*4*6=576 := by decide
      change (24*x^3*(4*x))*(6*x) = 576*x^5
      calc
        _ = (24*4*6)*x^5 := by
          simp only [Nat.pow_succ, Nat.pow_zero]
          ac_rfl
        _ = 576*x^5 := by rw [hc]

theorem sharp_budget_excludes_log_wall (n m : Nat)
    (hn : 42≤n)
    (hbudget : 2^m ≤576*(n+2)^5)
    (hwall : 2^(n-m)<n) : False := by
  let x := n+2
  have hgrowth : 576*x^6 < 2^n := by simpa only [x] using sharp_sextic_growth n hn
  have hbudgetx : 2^m ≤576*x^5 := hbudget
  have hm : m<n := by
    by_cases h : m<n
    · exact h
    have hnm : n≤m := by omega
    have hnmPow : 2^n ≤2^m := Nat.pow_le_pow_right (by decide) hnm
    have hx : 0<x := by dsimp [x]; omega
    have hpow5 : x^5 ≤ x^6 := Nat.pow_le_pow_right hx (by decide)
    have hsmall : 576*x^5 < 2^n := by
      have hh := Nat.mul_le_mul_left 576 hpow5
      omega
    omega
  have heq : 2^n=2^m*2^(n-m) := by
    calc
      2^n = 2^(m+(n-m)) := congrArg (fun e:Nat => 2^e) (by omega)
      _ = 2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
  have hmul : 2^m*2^(n-m) < (576*x^5)*n := by
    have hn0 : 0<2^m := Nat.pow_pos (by decide)
    have hA : 2^m*2^(n-m) < 2^m*n := Nat.mul_lt_mul_of_pos_left hwall hn0
    have hB : 2^m*n ≤ (576*x^5)*n := Nat.mul_le_mul_right n hbudgetx
    omega
  have hnx : n≤x := by dsimp [x]; omega
  have hlast : (576*x^5)*n ≤ 576*x^6 := by
    have hh := Nat.mul_le_mul_left (576*x^5) hnx
    calc
      _ ≤ (576*x^5)*x := hh
      _ = 576*x^6 := by
        calc
          _ = 576*(x^5*x) := by ac_rfl
          _ = 576*x^6 :=
            congrArg (fun a:Nat => 576*a) (Nat.pow_succ x 5).symm
  omega


#print axioms BB6.Agent50TwoReset.two_reset_sharp_budget
#print axioms BB6.Agent50TwoReset.sharp_budget_excludes_log_wall
end BB6.Agent50TwoReset
