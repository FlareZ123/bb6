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

#print axioms pow15_eq1
#print axioms pow27_eq7
#print axioms pow51_eq13
#print axioms pow99_ne19
end Agent17SheepPower
