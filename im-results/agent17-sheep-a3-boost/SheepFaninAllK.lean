import SheepFaninOriginal
import ThreeAdicOrder
namespace SheepFaninAllK

open BB6.Agent39Three (Q power_three_lifting)

theorem Q_lower : ∀k : Nat, 7 ≤ Q (k+1)
  | 0 => by decide
  | k+1 => by
      have ih := Q_lower k
      have hfac : 1 ≤ 1 + 3*(3^(k+1)*Q (k+1)) +
          (3^(k+1)*Q (k+1))*(3*(3^(k+1)*Q (k+1))) := by omega
      have hm := Nat.mul_le_mul_left (Q (k+1)) hfac
      change 7 ≤ Q ((k+1)+1)
      rw [Q]
      omega

/-- Fully constructive source quotient, without assuming an unproved
    exponential divisibility condition in downstream parent theorems. -/
theorem power_quotient (k h : Nat) (hk : 1 ≤ k) (hh : h ≤ k+1) :
    ∃ q : Nat, 7 ≤ q ∧ 3^h*q+1=2^(2*3^k) ∧
       (h ≤ k-1 → q%3=0) := by
  let q := 3^(k+1-h)*Q k
  have hpow : 3^h*3^(k+1-h)=3^(k+1) := by
    rw [←Nat.pow_add]
    congr 1
    omega
  have hQ : 7 ≤ Q k := by
    obtain ⟨r,hr⟩ : ∃r,k=r+1 := ⟨k-1,by omega⟩
    rw [hr]
    exact Q_lower r
  have hpowpos : 0 < 3^(k+1-h) := Nat.pow_pos (by decide)
  have hmul := Nat.mul_le_mul_right (Q k)
     (show 1 ≤ 3^(k+1-h) by omega)
  have hqmin : 7 ≤ q := by dsimp [q]; omega
  have htarget : 3^h*q+1=2^(2*3^k) := by
    calc
      3^h*q+1 = 3^(k+1)*Q k+1 := by
        dsimp [q]
        rw [←Nat.mul_assoc,hpow]
      _ = 2^(2*3^k) := by
        simpa only [Nat.add_comm] using (power_three_lifting k).symm
  refine ⟨q,hqmin,htarget,?_⟩
  intro hsmall
  have hd : 1 ≤ k+1-h := by omega
  have hdiv : 3 ∣ 3^(k+1-h) := by
    obtain ⟨r,hr⟩ : ∃r,k+1-h=r+1 := ⟨k-h,by omega⟩
    rw [hr,Nat.pow_succ]
    exact ⟨3^r,by omega⟩
  have hqdiv : 3 ∣ q := by
    dsimp [q]
    obtain ⟨r,hr⟩ := hdiv
    refine ⟨r*Q k, ?_⟩
    rw [hr]
    ac_rfl
  exact (Nat.dvd_iff_mod_eq_zero).mp hqdiv

theorem pow_index_even (s : Nat) : 2*3^(2*s)=2*9^s := by
  rw [Nat.pow_mul]

theorem pow_index_odd (s : Nat) : 2*3^(2*s+1)=2*(3*9^s) := by
  rw [Nat.pow_add,Nat.pow_mul]
  rw [show (3:Nat)^2=9 by decide, show (3:Nat)^1=3 by decide]
  ac_rfl

theorem a3_even_unconditional (s t : Nat)
    (hbound : 16*t+10 ≤ 2*s+1) :
    ∃ v, SheepEven.EvenEdge (8*v) (2^(2*3^(2*s))) := by
  have hk : 1 ≤ 2*s := by omega
  obtain ⟨q,hmin,hpow,_⟩ := power_quotient (2*s) (16*t+10) hk hbound
  have htarget : 3^(16*t+10)*q+1=2^(2*9^s) := by
    simpa only [pow_index_even] using hpow
  obtain ⟨v,hv⟩ := SheepFaninOriginal.a3_even_actual s t q htarget hmin
  exact ⟨v,by simpa only [←pow_index_even] using hv⟩

theorem a3_odd_unconditional (s t : Nat)
    (hbound : 16*t+14 ≤ 2*s+2) :
    ∃ v, SheepEven.EvenEdge (8*v) (2^(2*3^(2*s+1))) := by
  have hk : 1 ≤ 2*s+1 := by omega
  obtain ⟨q,hmin,hpow,_⟩ := power_quotient (2*s+1) (16*t+14) hk hbound
  have htarget : 3^(16*t+14)*q+1=2^(2*(3*9^s)) := by
    simpa only [pow_index_odd] using hpow
  obtain ⟨v,hv⟩ := SheepFaninOriginal.a3_odd_actual s t q htarget hmin
  exact ⟨v,by simpa only [←pow_index_odd] using hv⟩

theorem a6_unconditional (m t : Nat)
    (hbound : 21*t+20 ≤ 6*(m+1)-1) :
    ∃ v, SheepEven.EvenEdge (64*v) (2^(2*3^(6*(m+1)))) := by
  have hk : 1 ≤ 6*(m+1) := by omega
  have hle : 21*t+20 ≤ 6*(m+1)+1 := by omega
  obtain ⟨q,hmin,hpow,h3⟩ := power_quotient (6*(m+1)) (21*t+20) hk hle
  exact SheepFaninOriginal.a6_actual (m+1) t q hpow hmin (h3 hbound)

theorem a7_even_unconditional (s t : Nat)
    (hbound : 256*t+221 ≤ 2*s+1) :
    ∃ v, SheepEven.EvenEdge (128*v) (2^(2*3^(2*s))) := by
  have hk : 1 ≤ 2*s := by omega
  obtain ⟨q,hmin,hpow,_⟩ := power_quotient (2*s) (256*t+221) hk hbound
  have htarget : 3^(256*t+221)*q+1=2^(2*9^s) := by
    simpa only [pow_index_even] using hpow
  obtain ⟨v,hv⟩ := SheepFaninOriginal.a7_even_actual s t q htarget hmin
  exact ⟨v,by simpa only [←pow_index_even] using hv⟩

theorem a7_odd_unconditional (s t : Nat)
    (hbound : 256*t+83 ≤ 2*s+2) :
    ∃ v, SheepEven.EvenEdge (128*v) (2^(2*3^(2*s+1))) := by
  have hk : 1 ≤ 2*s+1 := by omega
  obtain ⟨q,hmin,hpow,_⟩ := power_quotient (2*s+1) (256*t+83) hk hbound
  have htarget : 3^(256*t+83)*q+1=2^(2*(3*9^s)) := by
    simpa only [pow_index_odd] using hpow
  obtain ⟨v,hv⟩ := SheepFaninOriginal.a7_odd_actual s t q htarget hmin
  exact ⟨v,by simpa only [←pow_index_odd] using hv⟩

#print axioms Q_lower
#print axioms power_quotient
#print axioms a3_even_unconditional
#print axioms a3_odd_unconditional
#print axioms a6_unconditional
#print axioms a7_even_unconditional
#print axioms a7_odd_unconditional
end SheepFaninAllK
