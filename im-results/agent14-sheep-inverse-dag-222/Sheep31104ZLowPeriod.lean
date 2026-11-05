import Std
set_option exponentiation.threshold 100000
namespace Sheep31104ZLowPeriod

private theorem pow_mod_period (m p r k : Nat) (hm : 1<m)
    (hp : 2^p % m=1) : 2^(r+p*k)%m=2^r%m := by
  rw [Nat.pow_add,Nat.pow_mul,Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m,hp]
  simp [Nat.mod_eq_of_lt hm]

theorem pow_mod_remainder (m p n : Nat) (hm : 1<m)
    (hp0 : 0<p) (hp : 2^p %m=1) :
    2^n%m = 2^(n%p)%m := by
  have he : n=n%p+p*(n/p) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div n p).symm
  calc
    2^n %m = 2^(n%p+p*(n/p)) %m := by rw [←he]
    _ = 2^(n%p)%m := pow_mod_period m p (n%p) (n/p) hm hp

/-- A finite full-period modular exclusion for every natural parameter. -/
theorem no_mod_eq_from_period (m p r P q K : Nat)
    (hm : 1<m) (hq : 0<q)
    (hp : 2^p %m=1) (hdiv : p ∣ P*q)
    (hbase : ∀ t<q, 2^(r+P*t)%m ≠ K%m) :
    ∀ k, 2^(r+P*k)%m ≠ K%m := by
  intro k
  let t := k%q
  have ht : t<q := Nat.mod_lt k hq
  obtain ⟨w,hw⟩ := hdiv
  have hk : k=t+q*(k/q) := by
    simpa [t,Nat.mul_comm] using (Nat.mod_add_div k q).symm
  have he : r+P*k = (r+P*t)+p*(w*(k/q)) := by
    calc
      r+P*k=r+P*(t+q*(k/q)) := congrArg (fun x => r+P*x) hk
      _ = (r+P*t)+(P*q)*(k/q) := by
        simp only [Nat.mul_add,Nat.mul_assoc]
        omega
      _ = (r+P*t)+p*(w*(k/q)) := by
        rw [hw]
        simp [Nat.mul_assoc]
  have hmod : 2^(r+P*k)%m=2^(r+P*t)%m := by
    rw [he]
    exact pow_mod_period m p (r+P*t) (w*(k/q)) hm hp
  rw [hmod]
  exact hbase t ht

#print axioms no_mod_eq_from_period
end Sheep31104ZLowPeriod
