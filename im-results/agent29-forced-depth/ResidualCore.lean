import ResidualPeriod
import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

theorem period_eq (L B : Nat)
    (hpow : 2^L=3*B+1) :
    2^(2*L)=3*((2^L+1)*B)+1 := by
  have heq : 2*L=L+L := by omega
  rw [heq,Nat.pow_add,hpow]
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

private theorem small_case (L B m v t:Nat)
    (hL : 0<L) (hm:0<m) (hBm:m≤B)
    (hv:v+2*m≤2*B) (ht:t<L) :
    ¬ ((2^L+1)*B ∣ v*2^t+m) := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  have hpBound : 2*2^t ≤ 2^L := by
    have he : 2*2^t = 2^(t+1) := by rw [Nat.pow_succ]; ac_rfl
    rw [he]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have ht1 : m ≤ (2*m)*2^t := by
    have hmul : (2*m)*1 ≤ (2*m)*(2^t) :=
      Nat.mul_le_mul_left (2*m) hp
    simp only [Nat.mul_one] at hmul
    omega
  have ht2 : v*2^t + m ≤ (v+2*m)*2^t := by
    calc
      v*2^t + m ≤ v*2^t +(2*m)*2^t := Nat.add_le_add_left ht1 _
      _ = (v+2*m)*2^t := by rw [Nat.add_mul]
  have ht3 : (v+2*m)*2^t ≤ (2*B)*2^t :=
    Nat.mul_le_mul_right _ hv
  have ht4 : (2*B)*2^t ≤ B*2^L := by
    calc
      (2*B)*2^t = B*(2*2^t) := by ac_rfl
      _ ≤ B*2^L := Nat.mul_le_mul_left _ hpBound
  have ht5 : B*2^L < (2^L+1)*B := by
    rw [Nat.add_mul]
    have hh : 2^L*B = B*2^L := Nat.mul_comm _ _
    omega
  have hbound : v*2^t+m < (2^L+1)*B := by omega
  intro hdiv
  have hle : (2^L+1)*B ≤ v*2^t+m :=
    Nat.le_of_dvd (by omega) hdiv
  omega


private theorem large_case (L B m v t:Nat)
    (hL:0<L) (hm:0<m) (hBm:m≤B) (hodd:B%2=1)
    (hpow:2^L=3*B+1)
    (hv:v+2*m≤2*B) (htlow:L≤t) (hthi:t<2*L) :
    ¬ ((2^L+1)*B ∣ v*2^t+m) := by
  let r := t-L
  let s := v*2^r
  let A := 2^L+1
  let Q := A*B
  have htr:t=L+r := by dsimp [r]; omega
  have hrL:r<L := by dsimp [r]; omega
  have hpowt : v*2^t = s*2^L := by
    dsimp [s]
    rw [htr,Nat.pow_add]
    ac_rfl
  have hpowBt : v*2^t+m = B*(3*s)+(s+m) := by
    rw [hpowt,hpow]
    dsimp [s]
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  have hpowAt : (v*2^t+m)+s = A*s+m := by
    rw [hpowt]
    dsimp [A]
    simp only [Nat.add_mul, Nat.mul_add]
    ac_rfl
  have hmA:m<A := by dsimp [A]; rw [hpow]; omega
  intro hdiv
  have hBdiv : B ∣ (v*2^t+m) := by
    have hf : B ∣ Q := by dsimp [Q]; exact Nat.dvd_mul_left B A
    exact Nat.dvd_trans hf (by simpa only [Q,A] using hdiv)
  have hBs : B ∣ s+m := by
    rw [hpowBt] at hBdiv
    exact (Nat.dvd_add_iff_right (Nat.dvd_mul_right B (3*s))).mpr hBdiv
  have hAdiv : A ∣ (v*2^t+m) := by
    have hf : A ∣ Q := Nat.dvd_mul_right A B
    exact Nat.dvd_trans hf (by simpa only [Q,A] using hdiv)
  have hAmod : (v*2^t+m)%A=0 := Nat.mod_eq_zero_of_dvd hAdiv
  have hsmod : s%A=m := by
    have hl : ((v*2^t+m)+s)%A = s%A := by
      rw [Nat.add_mod,hAmod]
      simp
    have hr : ((v*2^t+m)+s)%A = m%A := by
      rw [hpowAt,Nat.mul_add_mod]
    rw [Nat.mod_eq_of_lt hmA] at hr
    omega
  let u := s/A
  have hsu:s=m+A*u := by
    have hu := Nat.mod_add_div s A
    rw [hsmod] at hu
    dsimp [u]
    omega
  have hBs2 : B ∣ 2*(u+m) := by
    have heq : s+m = B*(3*u)+2*(u+m) := by
      rw [hsu]
      dsimp [A]
      rw [hpow]
      simp only [Nat.add_mul, Nat.mul_add]
      have hterm : 3*B*u=B*(3*u) := by ac_rfl
      rw [hterm]
      omega
    rw [heq] at hBs
    exact (Nat.dvd_add_iff_right (Nat.dvd_mul_right B (3*u))).mpr hBs
  have hBum : B ∣ u+m := by
    obtain ⟨z,hz⟩ := hBs2
    have hzmod : z%2=0 := by
      have hpar : (B*z)%2=0 := by rw [←hz]; omega
      rw [Nat.mul_mod,hodd] at hpar
      omega
    let w := z/2
    have hzeq:z=2*w := by
      dsimp [w]
      omega
    refine ⟨w,?_⟩
    rw [hzeq] at hz
    have heq : B*(2*w)=2*(B*w) := by ac_rfl
    rw [heq] at hz
    omega
  have humpos : 0 < u+m := Nat.lt_of_lt_of_le hm (Nat.le_add_left m u)
  have hBu : B ≤ u+m := Nat.le_of_dvd humpos hBum
  have hsp : u*2^L < s := by
    rw [hsu]
    dsimp [A]
    simp only [Nat.add_mul, Nat.mul_add]
    have hc:2^L*u=u*2^L := Nat.mul_comm _ _
    omega
  have hpowr: 2*2^r≤2^L := by
    have hp:2*2^r=2^(r+1) := by rw [Nat.pow_succ]; ac_rfl
    rw [hp]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hltmul : (2*u)*2^r < v*2^r := by
    have he : (2*u)*2^r = u*(2*2^r) := by ac_rfl
    have he_le: u*(2*2^r) ≤ u*2^L := Nat.mul_le_mul_left _ hpowr
    rw [he]
    dsimp [s] at hsp
    omega
  have huv : 2*u < v := Nat.lt_of_mul_lt_mul_right hltmul
  omega

/-- Rigorous arithmetic lower bound for every power-of-two congruence
    v*2^d + m divisible by the two-factor binary repunit Q. -/
theorem residual_barrier_core (L B m v d:Nat)
    (hL:0<L) (hm:0<m) (hBm:m≤B) (hodd:B%2=1)
    (hpow:2^L=3*B+1)
    (hdiv:((2^L+1)*B) ∣ v*2^d+m) :
    2*B < v+2*m := by
  by_cases hh:2*B<v+2*m
  · exact hh
  · have hv:v+2*m≤2*B := by omega
    have hperiod := period_eq L B hpow
    have hred := reduce_period ((2^L+1)*B) v m d L hL hperiod hdiv
    let t := d%(2*L)
    have ht:t<2*L := Nat.mod_lt _ (by omega)
    by_cases htlow:t<L
    · exact False.elim (small_case L B m v t hL hm hBm hv htlow
        (by simpa only [t] using hred))
    · exact False.elim (large_case L B m v t hL hm hBm hodd hpow hv
        (by omega) ht (by simpa only [t] using hred))
  
#print axioms period_eq
#print axioms small_case
#print axioms large_case
#print axioms residual_barrier_core
end BB6.Agent29Barrier
