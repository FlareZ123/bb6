import Lean
namespace SheepWeightedResidual
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2000

theorem base_period_reduce (a m p n : Nat) (hp : a^p % m = 1) :
    a^n % m = a^(n%p) % m := by
  have h : n = n%p + p*(n/p) := (Nat.mod_add_div n p).symm
  calc
    a^n % m = (a^(n%p) * (a^p)^(n/p)) % m :=
      (congrArg (fun e : Nat => a^e % m) h).trans (by rw [Nat.pow_add, Nat.pow_mul])
    _ = ((a^(n%p)%m) * ((a^p)^(n/p)%m))%m := Nat.mul_mod ..
    _ = a^(n%p)%m := by rw [Nat.pow_mod (a^p), hp]; simp

theorem residue_from_period (a m p r s B : Nat) (hp : 0<p)
    (hcycle : a^p%m=1)
    (hfinite : ∀ n : Fin p, a^n.val%m=r → n.val=s)
    (hr : a^B%m=r) : B%p=s := by
  rw [base_period_reduce a m p B hcycle] at hr
  exact hfinite ⟨B%p,Nat.mod_lt B hp⟩ hr

theorem residue_impossible (a m p r B : Nat) (hp : 0<p)
    (hcycle : a^p%m=1)
    (hfinite : ∀ n : Fin p, a^n.val%m≠r)
    (hr : a^B%m=r) : False := by
  rw [base_period_reduce a m p B hcycle] at hr
  exact hfinite ⟨B%p,Nat.mod_lt B hp⟩ hr

theorem linear_mod_inverse (C D M x k m i : Nat) (heq : C*x = D+M*k)
    (hm : M%m=0) (hi : (i*C)%m=1) : x%m=(i*D)%m := by
  have h := congrArg (fun n : Nat => (i*n)%m) heq
  rw [Nat.mul_assoc i C x |>.symm, Nat.mul_add] at h
  rw [Nat.mul_mod (i*C) x m, hi, Nat.one_mul, Nat.mod_mod] at h
  rw [Nat.add_mod (i*D) (i*(M*k)) m, ← Nat.mul_assoc i M k,
      Nat.mul_mod (i*M) k m, Nat.mul_mod i M m, hm] at h
  simpa using h

theorem terminal_linear (A C d e x k : Nat) (hx : 1≤x)
    (h : A*(d+e*k)=C*(x-1)) : C*x=A*d+C+(A*e)*k := by
  have h' : C*(x-1)+C=C*x := by calc
        C*(x-1)+C = C*((x-1)+1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = C*x := by rw [Nat.sub_add_cancel hx]
  calc
    C*x = C*(x-1)+C := h'.symm
    _ = A*d+C+(A*e)*k := by rw [← h, Nat.mul_add, Nat.mul_assoc]; ac_rfl

theorem type1_H0 (k B : Nat) (heq : 3^0*(5+135*k)=2^0*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 1*2^B=6+135*k := terminal_linear (3^0) (2^0) 5 135 (2^B) k hp heq
  clear heq hp
  have hm3 : 2^B%3=0 := linear_mod_inverse 1 6 135 (2^B) k 3 1 he (by decide) (by decide)
  clear he
  exact residue_impossible 2 3 2 0 B (by decide) (by decide) (by decide) hm3

theorem type1_H1 (k B : Nat) (heq : 3^1*(5+135*k)=2^1*(2^B-1)) : 32≤B := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 2*2^B=17+405*k := terminal_linear (3^1) (2^1) 5 135 (2^B) k hp heq
  clear heq hp
  have hm405 : 2^B%405=211 := linear_mod_inverse 2 17 405 (2^B) k 405 203 he (by decide) (by decide)
  clear he
  have hr405 := residue_from_period 2 405 108 211 32 B (by decide) (by decide) (by decide) hm405
  omega

theorem type1_H2 (k B : Nat) (heq : 3^2*(5+135*k)=2^2*(2^B-1)) : 32≤B := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 4*2^B=49+1215*k := terminal_linear (3^2) (2^2) 5 135 (2^B) k hp heq
  clear heq hp
  have hm1215 : 2^B%1215=316 := linear_mod_inverse 4 49 1215 (2^B) k 1215 304 he (by decide) (by decide)
  clear he
  have hr1215 := residue_from_period 2 1215 324 316 300 B (by decide) (by decide) (by decide) hm1215
  omega

theorem type3_H0 (k B : Nat) (heq : 3^0*(19+1683*k)=2^0*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 1*2^B=20+1683*k := terminal_linear (3^0) (2^0) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm9 : 2^B%9=2 := linear_mod_inverse 1 20 1683 (2^B) k 9 1 he (by decide) (by decide)
  have hm11 : 2^B%11=9 := linear_mod_inverse 1 20 1683 (2^B) k 11 1 he (by decide) (by decide)
  clear he
  have hr9 := residue_from_period 2 9 6 2 1 B (by decide) (by decide) (by decide) hm9
  have hr11 := residue_from_period 2 11 10 9 6 B (by decide) (by decide) (by decide) hm11
  omega

theorem type3_H1 (k B : Nat) (heq : 3^1*(19+1683*k)=2^1*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 2*2^B=59+5049*k := terminal_linear (3^1) (2^1) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm3 : 2^B%3=1 := linear_mod_inverse 2 59 5049 (2^B) k 3 2 he (by decide) (by decide)
  have hm11 : 2^B%11=2 := linear_mod_inverse 2 59 5049 (2^B) k 11 6 he (by decide) (by decide)
  clear he
  have hr3 := residue_from_period 2 3 2 1 0 B (by decide) (by decide) (by decide) hm3
  have hr11 := residue_from_period 2 11 10 2 1 B (by decide) (by decide) (by decide) hm11
  omega

theorem type3_H2 (k B : Nat) (heq : 3^2*(19+1683*k)=2^2*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 4*2^B=175+15147*k := terminal_linear (3^2) (2^2) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm17 : 2^B%17=14 := linear_mod_inverse 4 175 15147 (2^B) k 17 13 he (by decide) (by decide)
  clear he
  exact residue_impossible 2 17 8 14 B (by decide) (by decide) (by decide) hm17

theorem type3_H3 (k B : Nat) (heq : 3^3*(19+1683*k)=2^3*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 8*2^B=521+45441*k := terminal_linear (3^3) (2^3) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm17 : 2^B%17=12 := linear_mod_inverse 8 521 45441 (2^B) k 17 15 he (by decide) (by decide)
  clear he
  exact residue_impossible 2 17 8 12 B (by decide) (by decide) (by decide) hm17

theorem type3_H4 (k B : Nat) (heq : 3^4*(19+1683*k)=2^4*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 16*2^B=1555+136323*k := terminal_linear (3^4) (2^4) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm3 : 2^B%3=1 := linear_mod_inverse 16 1555 136323 (2^B) k 3 1 he (by decide) (by decide)
  have hm17 : 2^B%17=9 := linear_mod_inverse 16 1555 136323 (2^B) k 17 16 he (by decide) (by decide)
  clear he
  have hr3 := residue_from_period 2 3 2 1 0 B (by decide) (by decide) (by decide) hm3
  have hr17 := residue_from_period 2 17 8 9 7 B (by decide) (by decide) (by decide) hm17
  omega

theorem type3_H5 (k B : Nat) (heq : 3^5*(19+1683*k)=2^5*(2^B-1)) : 11502≤B := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 32*2^B=4649+408969*k := terminal_linear (3^5) (2^5) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm243 : 2^B%243=1 := linear_mod_inverse 32 4649 408969 (2^B) k 243 38 he (by decide) (by decide)
  have hm2187 : 2^B%2187=487 := linear_mod_inverse 32 4649 408969 (2^B) k 2187 1982 he (by decide) (by decide)
  have hm11 : 2^B%11=4 := linear_mod_inverse 32 4649 408969 (2^B) k 11 10 he (by decide) (by decide)
  have hm17 : 2^B%17=13 := linear_mod_inverse 32 4649 408969 (2^B) k 17 8 he (by decide) (by decide)
  clear he
  have hr243 := residue_from_period 2 243 162 1 0 B (by decide) (by decide) (by decide) hm243
  have hr11 := residue_from_period 2 11 10 4 2 B (by decide) (by decide) (by decide) hm11
  have hr17 := residue_from_period 2 17 8 13 6 B (by decide) (by decide) (by decide) hm17
  have hBform : B=162*(B/162) := by omega
  have hpow : 2^B=(2^162)^(B/162) := (congrArg (fun n : Nat => 2^n) hBform).trans (Nat.pow_mul ..)
  rw [hpow] at hm2187
  have hq := residue_from_period (2^162) 2187 9 487 8 (B/162) (by decide) (by decide) (by decide) hm2187
  clear hm243 hm2187 hm11 hm17 hpow
  have hr2187 : B%1458=1296 := by omega
  clear hq hBform hr243
  have hb : B=1296+1458*(B/1458) := by omega
  by_cases hn : 11502≤B
  · exact hn
  · 
    have ht : B/1458<7 := by omega
    omega

theorem type3_H6 (k B : Nat) (heq : 3^6*(19+1683*k)=2^6*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 64*2^B=13915+1226907*k := terminal_linear (3^6) (2^6) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm11 : 2^B%11=0 := linear_mod_inverse 64 13915 1226907 (2^B) k 11 5 he (by decide) (by decide)
  clear he
  exact residue_impossible 2 11 10 0 B (by decide) (by decide) (by decide) hm11

theorem type3_H7 (k B : Nat) (heq : 3^7*(19+1683*k)=2^7*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 128*2^B=41681+3680721*k := terminal_linear (3^7) (2^7) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm17 : 2^B%17=11 := linear_mod_inverse 128 41681 3680721 (2^B) k 17 2 he (by decide) (by decide)
  clear he
  exact residue_impossible 2 17 8 11 B (by decide) (by decide) (by decide) hm17

theorem type3_H8 (k B : Nat) (heq : 3^8*(19+1683*k)=2^8*(2^B-1)) : False := by
  have hp : 1≤2^B := Nat.one_le_pow B 2 (by decide)
  have he : 256*2^B=124915+11042163*k := terminal_linear (3^8) (2^8) 19 1683 (2^B) k hp heq
  clear heq hp
  have hm3 : 2^B%3=1 := linear_mod_inverse 256 124915 11042163 (2^B) k 3 1 he (by decide) (by decide)
  have hm11 : 2^B%11=7 := linear_mod_inverse 256 124915 11042163 (2^B) k 11 4 he (by decide) (by decide)
  clear he
  have hr3 := residue_from_period 2 3 2 1 0 B (by decide) (by decide) (by decide) hm3
  have hr11 := residue_from_period 2 11 10 7 7 B (by decide) (by decide) (by decide) hm11
  omega

theorem type1_terminal_low (k H B : Nat) (hH : H<3) (heq : 3^H*(5+135*k)=2^H*(2^B-1)) : 32≤B := by
  have hc : H=0 ∨ H=1 ∨ H=2 := by omega
  rcases hc with rfl|rfl|rfl
  · exact False.elim (type1_H0 k B heq)
  · exact type1_H1 k B heq
  · exact type1_H2 k B heq

theorem type3_terminal_low (k H B : Nat) (hH : H<9) (heq : 3^H*(19+1683*k)=2^H*(2^B-1)) : 11502≤B := by
  have hc : H=0 ∨ H=1 ∨ H=2 ∨ H=3 ∨ H=4 ∨ H=5 ∨ H=6 ∨ H=7 ∨ H=8 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact False.elim (type3_H0 k B heq)
  · exact False.elim (type3_H1 k B heq)
  · exact False.elim (type3_H2 k B heq)
  · exact False.elim (type3_H3 k B heq)
  · exact False.elim (type3_H4 k B heq)
  · exact type3_H5 k B heq
  · exact False.elim (type3_H6 k B heq)
  · exact False.elim (type3_H7 k B heq)
  · exact False.elim (type3_H8 k B heq)

#print axioms type1_terminal_low
#print axioms type3_terminal_low
end SheepWeightedResidual
