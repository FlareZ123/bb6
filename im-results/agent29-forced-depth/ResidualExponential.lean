import ResidualCore
import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

/-- The odd-index repunit B_r=(2^(2r+2)-1)/3 as a recurrence. -/
def oddRepunit : Nat → Nat
  | 0 => 1
  | r+1 => 4*oddRepunit r+1

theorem repunit_pow (r:Nat) : 2^(2*r+2)=3*oddRepunit r+1 := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he:2*(r+1)+2 = (2*r+2)+2 := by omega
      rw [he,Nat.pow_add,ih]
      simp only [oddRepunit]
      omega

theorem repunit_odd (r:Nat) : oddRepunit r % 2=1 := by
  induction r with
  | zero => decide
  | succ r ih =>
      simp only [oddRepunit]
      omega

theorem repunit_ge (r:Nat) : 2*r+1≤oddRepunit r := by
  induction r with
  | zero => decide
  | succ r ih =>
      simp only [oddRepunit]
      omega

/-- Exact arithmetic consequence of the original Machine C second stopping
    locus and any dyadic inverse residual scaling, for all odd m. -/
theorem second_stop_odd_residual_exponential
    (j m k d Y:Nat) (hpos:1≤m) (hodd:m%2=1)
    (hstop:k+j+3*m+5 = 2^(2*m+2)*(j+3))
    (hscale:2^d*(Y+2)=k+2) :
    2^(m+2) ≤ Y+6*m+1 := by
  let r := m/2
  have hm : m=2*r+1 := by dsimp [r]; omega
  let B:=oddRepunit r
  let L:=m+1
  let Q:=(2^L+1)*B
  have hL:0<L := by dsimp [L]; omega
  have hBm:m≤B := by
    dsimp [B]
    rw [hm]
    exact repunit_ge r
  have hBodd:B%2=1 := repunit_odd r
  have hpow : 2^L=3*B+1 := by
    dsimp [L,B]
    rw [hm]
    have he : (2*r+1)+1=2*r+2 := by omega
    rw [he]
    exact repunit_pow r
  have hperiod:2^(2*L)=3*Q+1 := period_eq L B hpow
  have hpowStop : 2^(2*m+2)=3*Q+1 := by
    have he : 2*m+2=2*L := by dsimp [L]; omega
    rw [he]
    exact hperiod
  have h_eq : 2^d*(Y+2)+3*m=3*Q*(j+3) := by
    have hs := hstop
    rw [hpowStop] at hs
    have heq : (3*Q+1)*(j+3)=3*Q*(j+3)+(j+3) := by
      rw [Nat.add_mul]
      omega
    rw [heq] at hs
    omega
  have h3 : 3 ∣ 2^d*(Y+2) := by
    have hdiv : 3 ∣ 2^d*(Y+2)+3*m := by
      rw [h_eq]
      have heq: 3*Q*(j+3)=3*(Q*(j+3)) := by ac_rfl
      rw [heq]
      exact Nat.dvd_mul_right 3 _
    exact (Nat.dvd_add_iff_left (Nat.dvd_mul_right 3 m)).mpr hdiv
  have h3Y : 3 ∣ Y+2 :=
    (Nat.Coprime.pow_right d (by decide : (3:Nat).Coprime 2)).dvd_of_dvd_mul_left h3
  obtain ⟨v,hv⟩ := h3Y
  have hvpos:0<v := by omega
  have hQ : Q ∣ v*2^d+m := by
    have heq3 : 3*(v*2^d+m)=3*(Q*(j+3)) := by
      rw [hv] at h_eq
      have heq1 : 2^d*(3*v)=3*(v*2^d) := by ac_rfl
      have heq2 : 3*Q*(j+3)=3*(Q*(j+3)) := by ac_rfl
      rw [heq1,heq2] at h_eq
      omega
    have heq : v*2^d+m=Q*(j+3) := by omega
    refine ⟨j+3,?_⟩
    simpa [Nat.mul_comm] using heq
  have hb := residual_barrier_core L B m v d hL (by omega)
      hBm hBodd hpow (by simpa only [Q] using hQ)
  have he : 2^(m+2)=2*(2^L) := by
    have hmeq:m+2=L+1 := by dsimp [L]
    rw [hmeq,Nat.pow_succ]
    ac_rfl
  have hyplus : Y+2=3*v := hv
  rw [he,hpow]
  omega

#print axioms oddRepunit
#print axioms repunit_pow
#print axioms repunit_odd
#print axioms repunit_ge
#print axioms second_stop_odd_residual_exponential
end BB6.Agent29Barrier
