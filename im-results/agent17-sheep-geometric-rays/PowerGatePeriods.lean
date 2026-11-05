import Std

namespace Agent17SheepPower

private theorem pow_mod_reduce (m p n : Nat) (_hm : 0 < m) (_hp : 0 < p)
    (hperiod : (2:Nat)^p % m = 1) :
    (2:Nat)^n % m = (2:Nat)^(n%p) % m := by
  have he : n = n % p + p * (n / p) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div n p).symm
  calc
    (2:Nat)^n % m = 2^(n%p+p*(n/p))%m := congrArg (fun x => (2:Nat)^x %m) he
    _ = (2^(n%p) * (2^p)^(n/p))%m := by rw [Nat.pow_add, Nat.pow_mul]
    _ = ((2^(n%p)%m) * (((2^p)^(n/p))%m))%m := by rw [Nat.mul_mod]
    _ = ((2^(n%p)%m) * (((2^p%m)^(n/p))%m))%m := by
      exact congrArg (fun v : Nat => ((2^(n%p)%m)*v)%m) (Nat.pow_mod (2^p) (n/p) m)
    _ = (2:Nat)^(n%p)%m := by simp [hperiod]

private theorem high_k_gap_shift (n : Nat) :
    1 < 6*(n+5)-5 ∧ 6*(n+5)-5 < (2:Nat)^(n+5) := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hpow : (2:Nat)^(n+1+5) = 2*2^(n+5) := by
        rw [show n+1+5=(n+5)+1 by omega, Nat.pow_succ]
        omega
      have hbig : 6 ≤ (2:Nat)^(n+5) := by
        have hx : (2:Nat)^5 ≤ (2:Nat)^(n+5) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        omega
      rw [hpow]
      omega

theorem high_k_gap_bound (a : Nat) (ha : 5 ≤ a) :
    1 < 6*a-5 ∧ 6*a-5 < (2:Nat)^a := by
  have heq : a-5+5=a := by omega
  simpa only [heq] using high_k_gap_shift (a-5)

theorem pow9_eq1 (n : Nat) : (2:Nat)^n % 9 = 1 ↔ n % 6 = 0 := by
  have hperiod : (2:Nat)^6 % 9 = 1 := by decide
  have hred := pow_mod_reduce 9 6 n (by decide) (by decide) hperiod
  have hlt : n%6 <6 := Nat.mod_lt _ (by omega)
  have hsmall : ∀ r : Fin 6, ((2:Nat)^r.val % 9 = 1 ↔ r.val = 0) := by decide
  rw [hred]
  exact hsmall ⟨n%6,hlt⟩

theorem pow15_eq1 (n : Nat) : (2:Nat)^n % 15 = 1 ↔ n % 4 = 0 := by
  have hperiod : (2:Nat)^4 % 15 = 1 := by decide
  have hred := pow_mod_reduce 15 4 n (by decide) (by decide) hperiod
  have hlt : n%4 <4 := Nat.mod_lt _ (by omega)
  have hsmall : ∀ r : Fin 4, ((2:Nat)^r.val % 15 = 1 ↔ r.val = 0) := by decide
  rw [hred]
  exact hsmall ⟨n%4,hlt⟩

theorem pow27_eq7 (n : Nat) : (2:Nat)^n % 27 = 7 ↔ n % 18 = 16 := by
  have hperiod : (2:Nat)^18 % 27 = 1 := by decide
  have hred := pow_mod_reduce 27 18 n (by decide) (by decide) hperiod
  have hlt : n%18 <18 := Nat.mod_lt _ (by omega)
  have hsmall : ∀ r : Fin 18, ((2:Nat)^r.val % 27 = 7 ↔ r.val = 16) := by decide
  rw [hred]
  exact hsmall ⟨n%18,hlt⟩

theorem pow51_eq13 (n : Nat) : (2:Nat)^n % 51 = 13 ↔ n % 8 = 6 := by
  have hperiod : (2:Nat)^8 % 51 = 1 := by decide
  have hred := pow_mod_reduce 51 8 n (by decide) (by decide) hperiod
  have hlt : n%8 <8 := Nat.mod_lt _ (by omega)
  have hsmall : ∀ r : Fin 8, ((2:Nat)^r.val % 51 = 13 ↔ r.val = 6) := by decide
  rw [hred]
  exact hsmall ⟨n%8,hlt⟩

theorem pow99_ne19 (n : Nat) : (2:Nat)^n % 99 ≠ 19 := by
  have hperiod : (2:Nat)^30%99=1 := by decide
  have hred := pow_mod_reduce 99 30 n (by omega) (by omega) hperiod
  have hlt : n%30 <30 := Nat.mod_lt _ (by omega)
  have hsmall : ∀ r : Fin 30, (2:Nat)^r.val % 99 ≠ 19 := by decide
  rw [hred]
  exact hsmall ⟨n%30,hlt⟩

theorem pow45_ne44 (n : Nat) : (2:Nat)^n % 45 ≠ 44 := by
  have hp : (2:Nat)^12 % 45 = 1 := by decide
  have hred := pow_mod_reduce 45 12 n (by decide) (by decide) hp
  have hlt : n%12 < 12 := Nat.mod_lt _ (by omega)
  have hfinite : ∀ r : Fin 12, (2:Nat)^r.val % 45 ≠ 44 := by decide
  rw [hred]
  exact hfinite ⟨n%12,hlt⟩

theorem pow153_ne35 (n : Nat) : (2:Nat)^n % 153 ≠ 35 := by
  have hp : (2:Nat)^24 % 153 = 1 := by decide
  have hred := pow_mod_reduce 153 24 n (by decide) (by decide) hp
  have hlt : n%24 < 24 := Nat.mod_lt _ (by omega)
  have hfinite : ∀ r : Fin 24, (2:Nat)^r.val % 153 ≠ 35 := by decide
  rw [hred]
  exact hfinite ⟨n%24,hlt⟩

theorem pow297_ne53 (n : Nat) : (2:Nat)^n % 297 ≠ 53 := by
  have hp : (2:Nat)^90 % 297 = 1 := by decide
  have hred := pow_mod_reduce 297 90 n (by decide) (by decide) hp
  have hlt : n%90 < 90 := Nat.mod_lt _ (by omega)
  have hfinite : ∀ r : Fin 90, (2:Nat)^r.val % 297 ≠ 53 := by decide
  rw [hred]
  exact hfinite ⟨n%90,hlt⟩

theorem pow585_ne71 (n : Nat) : (2:Nat)^n % 585 ≠ 71 := by
  have hp : (2:Nat)^12 % 585 = 1 := by decide
  have hred := pow_mod_reduce 585 12 n (by decide) (by decide) hp
  have hlt : n%12 < 12 := Nat.mod_lt _ (by omega)
  have hfinite : ∀ r : Fin 12, (2:Nat)^r.val % 585 ≠ 71 := by decide
  rw [hred]
  exact hfinite ⟨n%12,hlt⟩

theorem pow1161_ne89 (n : Nat) : (2:Nat)^n % 1161 ≠ 89 := by
  have hp : (2:Nat)^126 % 1161 = 1 := by decide
  have hred := pow_mod_reduce 1161 126 n (by decide) (by decide) hp
  have hlt : n%126 < 126 := Nat.mod_lt _ (by omega)
  have hfinite : ∀ r : Fin 126, (2:Nat)^r.val % 1161 ≠ 89 := by decide
  rw [hred]
  exact hfinite ⟨n%126,hlt⟩

theorem pow81_eq17 (n : Nat) : (2:Nat)^n % 81 = 17 ↔ n % 54 = 33 := by
  have hp : (2:Nat)^54 % 81 = 1 := by decide
  have hred := pow_mod_reduce 81 54 n (by decide) (by decide) hp
  have hlt : n%54 <54 := Nat.mod_lt _ (by omega)
  have hfinite : ∀ r : Fin 54, ((2:Nat)^r.val % 81 = 17 ↔ r.val = 33) := by decide
  rw [hred]
  exact hfinite ⟨n%54,hlt⟩

#print axioms pow45_ne44
#print axioms pow81_eq17
#print axioms pow153_ne35
#print axioms pow297_ne53
#print axioms pow585_ne71
#print axioms pow1161_ne89

#print axioms high_k_gap_bound
#print axioms pow9_eq1
#print axioms pow15_eq1
#print axioms pow27_eq7
#print axioms pow51_eq13
#print axioms pow99_ne19
end Agent17SheepPower
