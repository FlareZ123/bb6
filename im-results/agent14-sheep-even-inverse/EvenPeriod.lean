import Std
set_option maxRecDepth 32768
set_option exponentiation.threshold 10000

namespace SheepEvenCert

/-- Verify periodicity modulo an odd modulus using a certificate 2^p%m=1. -/
theorem pow_mod_period (m p r k : Nat) (hm : 1 < m)
    (hp : 2^p % m = 1) :
    2^(r+p*k) % m = 2^r % m := by
  rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod]
  rw [Nat.pow_mod (2^p) k m, hp]
  simp [Nat.mod_eq_of_lt hm]

/-- Modulo twice the odd modulus, positive powers retain the same period. -/
theorem pow_mod_twice_period (m p r k : Nat) (hm : 1 < m)
    (hp : 2^p % m = 1) (hr : 0 < r) :
    2^(r+p*k) % (2*m) = 2^r % (2*m) := by
  have heq := pow_mod_period m p (r-1) k hm hp
  have hleft : 2^(r+p*k) % (2*m) = 2*(2^(r-1+p*k)%m) := by
    have h : r+p*k=(r-1+p*k)+1 := by omega
    rw [h, Nat.pow_succ]
    rw [show 2*m=m*2 by omega, Nat.mul_mod_mul_right]
    omega
  have hright : 2^r % (2*m) = 2*(2^(r-1)%m) := by
    have hpowsucc : 2^r = 2^(r-1)*2 := by
      calc
        2^r = 2^((r-1)+1) := by congr 1
        _ = 2^(r-1)*2 := by rw [Nat.pow_succ]
    rw [hpowsucc]
    rw [show 2*m=m*2 by omega, Nat.mul_mod_mul_right]
    omega
  rw [hleft, hright, heq]

/-- Exhaustively excluding one finite modular period proves an all-k result. -/
theorem no_mod_zero_from_period (modulus p R M q b : Nat)
    (hm : 1 < modulus) (hq : 0 < q)
    (hp : 2^p % modulus = 1)
    (hpdiv : p ∣ M*q)
    (hbase : ∀ t < q, (2^(R+M*t)+b) % modulus ≠ 0) :
    ∀ k, (2^(R+M*k)+b) % modulus ≠ 0 := by
  intro k
  let t := k % q
  have ht : t < q := Nat.mod_lt k hq
  obtain ⟨w, hw⟩ := hpdiv
  have hk : k = t + q*(k/q) := by
    simpa [t, Nat.mul_comm] using (Nat.mod_add_div k q).symm
  have he : R+M*k = (R+M*t)+p*(w*(k/q)) := by
    calc
      R+M*k = R+M*(t+q*(k/q)) := congrArg (fun x => R+M*x) hk
      _ = (R+M*t)+(M*q)*(k/q) := by
        simp only [Nat.mul_add, Nat.mul_assoc]
        omega
      _ = (R+M*t)+p*(w*(k/q)) := by
        rw [hw]
        simp [Nat.mul_assoc]
  have hmod : 2^(R+M*k) % modulus = 2^(R+M*t) % modulus := by
    rw [he]
    exact pow_mod_period modulus p (R+M*t) (w*(k/q)) hm hp
  have hcalc : (2^(R+M*k)+b) % modulus =
      (2^(R+M*t)+b) % modulus := by
    rw [Nat.add_mod, hmod, ←Nat.add_mod]
  rw [hcalc]
  exact hbase t ht

/-- All-k disqualification of a designated residue modulo twice an odd modulus. -/
theorem no_twice_value_from_period (modulus p R M q b target : Nat)
    (hm : 1 < modulus) (hR : 0 < R) (hq : 0 < q)
    (hp : 2^p % modulus = 1) (hpdiv : p ∣ M*q)
    (hbase : ∀ t < q, (2^(R+M*t)+b) % (2*modulus) ≠ target) :
    ∀ k, (2^(R+M*k)+b) % (2*modulus) ≠ target := by
  intro k
  let t := k%q
  have ht : t<q := Nat.mod_lt k hq
  obtain ⟨w,hw⟩ := hpdiv
  have hk : k=t+q*(k/q) := by
    simpa [t, Nat.mul_comm] using (Nat.mod_add_div k q).symm
  have he : R+M*k=(R+M*t)+p*(w*(k/q)) := by
    calc
      R+M*k=R+M*(t+q*(k/q)) := congrArg (fun x => R+M*x) hk
      _=(R+M*t)+(M*q)*(k/q) := by
        simp only [Nat.mul_add,Nat.mul_assoc]; omega
      _=(R+M*t)+p*(w*(k/q)) := by rw [hw]; simp [Nat.mul_assoc]
  have hmod : 2^(R+M*k)%(2*modulus)=2^(R+M*t)%(2*modulus) := by
    rw [he]
    exact pow_mod_twice_period modulus p (R+M*t) (w*(k/q)) hm hp (by omega)
  have hcalc : (2^(R+M*k)+b)%(2*modulus)=
      (2^(R+M*t)+b)%(2*modulus) := by
    rw [Nat.add_mod,hmod,←Nat.add_mod]
  rw [hcalc]
  exact hbase t ht

/-- Uniform two-congruence elimination, used for parity-correct generic inverses. -/
theorem no_joint_period (m1 m2 p R1 R2 M q c1 c2 : Nat)
    (hm1 : 1 < m1) (hm2 : 1 < m2)
    (hR2 : 0 < R2) (hq : 0 < q)
    (hp1 : 2^p % m1 = 1) (hp2 : 2^p % m2 = 1)
    (hpdiv : p ∣ M*q)
    (hbase : ∀ t < q, ¬ ((2^(R1+M*t)+c1)%m1=0 ∧
                (2^(R2+M*t)+c2)%(2*m2)=m2)) :
    ∀ k, ¬ ((2^(R1+M*k)+c1)%m1=0 ∧
                (2^(R2+M*k)+c2)%(2*m2)=m2) := by
  intro k
  let t := k%q
  have ht : t<q := Nat.mod_lt k hq
  obtain ⟨w,hw⟩ := hpdiv
  have hk : k=t+q*(k/q) := by
    simpa [t, Nat.mul_comm] using (Nat.mod_add_div k q).symm
  have he (R : Nat) : R+M*k=(R+M*t)+p*(w*(k/q)) := by
    calc
      R+M*k=R+M*(t+q*(k/q)) := congrArg (fun x => R+M*x) hk
      _=(R+M*t)+(M*q)*(k/q) := by
        simp only [Nat.mul_add, Nat.mul_assoc]; omega
      _=(R+M*t)+p*(w*(k/q)) := by rw [hw]; simp [Nat.mul_assoc]
  have h1 : 2^(R1+M*k)%m1=2^(R1+M*t)%m1 := by
    rw [he R1]
    exact pow_mod_period m1 p (R1+M*t) (w*(k/q)) hm1 hp1
  have h2 : 2^(R2+M*k)%(2*m2)=2^(R2+M*t)%(2*m2) := by
    rw [he R2]
    exact pow_mod_twice_period m2 p (R2+M*t) (w*(k/q)) hm2 hp2 (by omega)
  have hc1 : (2^(R1+M*k)+c1)%m1=(2^(R1+M*t)+c1)%m1 := by
    rw [Nat.add_mod,h1,←Nat.add_mod]
  have hc2 : (2^(R2+M*k)+c2)%(2*m2)=(2^(R2+M*t)+c2)%(2*m2) := by
    rw [Nat.add_mod,h2,←Nat.add_mod]
  intro hc
  exact hbase t ht ⟨hc1.symm.trans hc.1, hc2.symm.trans hc.2⟩

/-- An authentic nontrivial period-two residue pair in the Sheep 138 certificate. -/
theorem p1_h0_a3_excluded (k : Nat) :
    ¬ ((2^(141+4860*k)+13)%15=0 ∧
       (2^(142+4860*k)+431)%510=255) := by
  apply no_joint_period 15 255 8 141 142 4860 2 13 431
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro t ht
    have ht01 : t=0 ∨ t=1 := by omega
    rcases ht01 with h|h
    · subst t; decide
    · subst t; decide

/-- For r=138 the root h=0,a=1 generic inverse is impossible. -/
theorem root_h0a1_excluded (k : Nat) :
    (2^(139+4860*k)+9)%10≠5 := by
  apply no_twice_value_from_period 5 4 139 4860 1 9 5
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro t ht
    have h : t=0 := by omega
    subst t
    decide

#print axioms no_twice_value_from_period
#print axioms root_h0a1_excluded

#print axioms pow_mod_period
#print axioms pow_mod_twice_period
#print axioms no_mod_zero_from_period
#print axioms no_joint_period
#print axioms p1_h0_a3_excluded

end SheepEvenCert
