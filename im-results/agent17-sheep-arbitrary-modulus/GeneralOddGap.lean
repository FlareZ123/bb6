import Std
import Lean.Elab.Tactic.Omega
namespace BB6Sheep17Gap
private theorem small_nonmultiple (R w z : Int)
    (hp : 0 < R) (ha : 0 < w) (hb : w < R)
    (h : R*z = w) : False := by
  by_cases hz : z ≤ 0
  · have hm : R*z ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hz
    omega
  · have hz1 : 1 ≤ z := by omega
    have hm := Int.mul_le_mul_of_nonneg_left hz1 (show 0 ≤ R by omega)
    omega

private theorem high_pos_impossible
    (c K M R z q : Int)
    (hc : c < K) (hr : c+K < R) (hq0 : 0 ≤ q) (hq : q < c)
    (hm : M = R*z+1) (he : c*R = q*M+K) : False := by
  have h1 : R*(c-q*z) = c*R-q*(R*z) := by
    calc
      R*(c-q*z) = R*c-R*(q*z) := by rw [Int.mul_sub]
      _ = c*R-q*(R*z) := by congr 1 <;> ac_rfl
  have h2 : q*(R*z+1) = q*(R*z)+q := by
    simp only [Int.mul_add, Int.mul_one]
  have h3 : R*(c-q*z) = q+K := by
    rw [h1]
    rw [hm, h2] at he
    omega
  exact small_nonmultiple R (q+K) (c-q*z) (by omega) (by omega) (by omega) h3

private theorem high_neg_impossible
    (c K M R z q : Int)
    (hc : c < K) (hr : c+K < R) (hq0 : 0 ≤ q) (hq : q < c)
    (hm : M = R*z+1) (he : c*R+K = (q+1)*M) : False := by
  have h1 : R*((q+1)*z-c) = (q+1)*(R*z)-c*R := by
    calc
      R*((q+1)*z-c) = R*((q+1)*z)-R*c := by rw [Int.mul_sub]
      _ = (q+1)*(R*z)-c*R := by congr 1 <;> ac_rfl
  have h2 : (q+1)*(R*z+1) = (q+1)*(R*z)+(q+1) := by
    simp only [Int.mul_add, Int.mul_one]
  have h3 : R*((q+1)*z-c) = K-q-1 := by
    rw [h1]
    rw [hm, h2] at he
    omega
  exact small_nonmultiple R (K-q-1) ((q+1)*z-c)
     (by omega) (by omega) (by omega) h3

#print axioms high_pos_impossible
#print axioms high_neg_impossible
end BB6Sheep17Gap

namespace BB6Sheep17Gap
private theorem middle_multiple (M V : Int)
    (hm : 0<M) (hl : 0<V) (hu : V<2*M) (hd : V%M=0) : V=M := by
  have hdiv : M ∣ V := Int.dvd_of_emod_eq_zero hd
  obtain ⟨q,hq⟩ := hdiv
  by_cases hq0 : q≤0
  · have hn : M*q≤0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hq0
    omega
  · by_cases hq2 : 2≤q
    · have hn : M*2≤M*q := Int.mul_le_mul_of_nonneg_left hq2 (by omega)
      omega
    · have heq : q=1 := by omega
      rw [heq] at hq
      simp only [Int.mul_one] at hq
      exact hq
#print axioms middle_multiple
end BB6Sheep17Gap

namespace BB6Sheep17Gap
/-- A uniform modular gap for any positive coefficient c and odd target K.
The residue representative R may be any positive even divisor of M-1.
The bound on M ensures no positive or negative signed residue match. -/
theorem generalized_odd_gap (c K M R z : Int)
    (hc : 0<c) (hk : c<K) (hkodd : K%2=1)
    (hre : R%2=0) (hrp : 0<R) (hrm : R<M)
    (hm : M=R*z+1) (hstrong : c*(c+K)+K<M) :
    (c*R)%M ≠ K ∧ (c*R+K)%M ≠ 0 := by
  have hmp : 0<M := by omega
  have hkp : 0<K := by omega
  have hklt : K<M := by
    have hmul : 0 ≤ c*(c+K) := Int.mul_nonneg (by omega) (by omega)
    omega
  let v : Int := c*R
  let q : Int := v/M
  have hvp : 0<v := Int.mul_pos hc hrp
  have hqp : 0≤q := Int.ediv_nonneg (by omega) (by omega)
  have hqm : q<c := by
    apply Int.ediv_lt_of_lt_mul hmp
    exact Int.mul_lt_mul_of_pos_left hrm hc
  have hremp : 0 ≤ v%M := Int.emod_nonneg v (by omega)
  have hreml : v%M < M := Int.emod_lt_of_pos v hmp
  have hdecomp : M*q+v%M=v := Int.mul_ediv_add_emod v M
  by_cases hsmall : R ≤ c+K
  · have hvbound : v ≤ c*(c+K) := Int.mul_le_mul_of_nonneg_left hsmall (by omega)
    have hvplus : 0<v+K ∧ v+K<M := by omega
    have hvrem : v%M=v := Int.emod_eq_of_lt (by omega) (by omega)
    have heven : v%2=0 := by
      change (c*R)%2=0
      rw [Int.mul_emod, hre]
      simp
    constructor
    · intro h
      rw [hvrem] at h
      rw [h] at heven
      omega
    · intro h
      have hmod : (v+K)%M=v+K := Int.emod_eq_of_lt (by omega) hvplus.2
      rw [hmod] at h
      omega
  · have hbig : c+K<R := by omega
    constructor
    · intro h
      have he : c*R = q*M+K := by
        change (c*R)%M=K at h
        rw [h] at hdecomp
        dsimp [v] at hdecomp
        rw [Int.mul_comm M q] at hdecomp
        omega
      exact high_pos_impossible c K M R z q hk hbig hqp hqm hm he
    · intro h
      have hsumzero : (v%M+K)%M=0 := by
        rw [Int.emod_add_emod]
        exact h
      have hsumgt : 0 < v%M+K := by omega
      have hsumlt : v%M+K < 2*M := by omega
      have hsum : v%M+K=M := middle_multiple M (v%M+K) hmp hsumgt hsumlt hsumzero
      have hmul : (q+1)*M = q*M+M := by simp only [Int.add_mul, Int.one_mul]
      have he' : c*R+K=q*M+M := by
        dsimp [v] at hdecomp hsum
        rw [Int.mul_comm M q] at hdecomp
        omega
      have he : c*R+K=(q+1)*M := by
        rw [hmul]
        exact he' 
      exact high_neg_impossible c K M R z q hk hbig hqp hqm hm he

#print axioms generalized_odd_gap
end BB6Sheep17Gap

namespace BB6Sheep17Gap
/-- Turn the signed modular exclusion into a pair of nondivisibility statements. -/
theorem generalized_gap_no_divisors (c K M R z : Int)
    (hc : 0<c) (hk : c<K) (hkodd : K%2=1)
    (hre : R%2=0) (hrp : 0<R) (hrm : R<M)
    (hm : M=R*z+1) (hstrong : c*(c+K)+K<M) :
    (¬ M ∣ c*R-K) ∧ (¬ M ∣ c*R+K) := by
  have h := generalized_odd_gap c K M R z hc hk hkodd hre hrp hrm hm hstrong
  have hmp : 0<M := by omega
  have hkp : 0<K := by omega
  have hkl : K<M := by
    have hmul : 0 ≤ c*(c+K) := Int.mul_nonneg (by omega) (by omega)
    omega
  constructor
  · intro hd
    have hs : (c*R)%M=K%M :=
      (Int.emod_eq_emod_iff_emod_sub_eq_zero).2 (Int.emod_eq_zero_of_dvd hd)
    have hkr : K%M=K := Int.emod_eq_of_lt (by omega) hkl
    rw [hkr] at hs
    exact h.1 hs
  · intro hd
    exact h.2 (Int.emod_eq_zero_of_dvd hd)
#print axioms generalized_gap_no_divisors
end BB6Sheep17Gap

namespace BB6Sheep17Gap
private theorem flip_nondivisibility (M K x y : Int)
    (hs : M ∣ x+y)
    (hp : ¬M ∣ y-K) (hn : ¬M ∣ y+K) :
    (¬M ∣ x-K) ∧ (¬M ∣ x+K) := by
  constructor
  · intro h
    have ht : M ∣ (x+y)-(x-K) := Int.dvd_sub hs h
    have hh : (x+y)-(x-K) = y+K := by omega
    rw [hh] at ht
    exact hn ht
  · intro h
    have ht : M ∣ (x+y)-(x+K) := Int.dvd_sub hs h
    have hh : (x+y)-(x+K) = y-K := by omega
    rw [hh] at ht
    exact hp ht
#print axioms flip_nondivisibility
end BB6Sheep17Gap

namespace BB6Sheep17Gap
private theorem small_coefficient_base (c K M : Int)
    (hc : 0<c) (hk : c<K) (hm : c+K<M) :
    (¬M ∣ c-K) ∧ (¬M ∣ c+K) := by
  constructor
  · intro h
    have hd : M ∣ K-c := by
      have hh : M ∣ -(c-K) := (Int.dvd_neg).2 h
      have heq : K-c = -(c-K) := by omega
      rw [heq]
      exact hh
    obtain ⟨z,hz⟩ := hd
    exact small_nonmultiple M (K-c) z (by omega) (by omega) (by omega) hz.symm
  · intro h
    obtain ⟨z,hz⟩ := h
    exact small_nonmultiple M (c+K) z (by omega) (by omega) (by omega) hz.symm
#print axioms small_coefficient_base
end BB6Sheep17Gap

namespace BB6Sheep17Gap
/-- All-exponent modular gap, without Mathlib or an unverified modular period.
For fixed c>0 and odd K>c, a single finite exponential bound rules out
both residue signs at every exponent. -/
theorem no_power_signed_gap (a : Nat) (c K : Int)
    (hc : 0<c) (hk : c<K) (hkodd : K%2=1)
    (hstrong : c*(c+K)+K < (2:Int)^(a+1)+1) :
    ∀ n : Nat,
      (¬ ((2:Int)^(a+1)+1) ∣ c*(2:Int)^n-K) ∧
      (¬ ((2:Int)^(a+1)+1) ∣ c*(2:Int)^n+K) := by
  let M : Int := (2:Int)^(a+1)+1
  have hmp : 0<M := by
    have hh : 0<(2:Int)^(a+1) := Int.pow_pos (by decide)
    dsimp [M]
    omega
  have hcplus : c+K<M := by
    have hck : 1 ≤ c+K := by omega
    have hmul : c ≤ c*(c+K) := by
      have hh := Int.mul_le_mul_of_nonneg_left hck (by omega : 0≤c)
      simpa only [Int.mul_one] using hh
    dsimp [M] at *
    omega
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hna : n ≤ a
    · cases n with
      | zero =>
          change (¬M ∣ c*(2:Int)^0-K) ∧ (¬M ∣ c*(2:Int)^0+K)
          simp only [Int.pow_zero, Int.mul_one]
          exact small_coefficient_base c K M hc hk hcplus
      | succ r =>
          let R : Int := (2:Int)^(r+1)
          let z : Int := (2:Int)^((a+1)-(r+1))
          have hrp : 0<R := Int.pow_pos (by decide)
          have hzp : 0<z := Int.pow_pos (by decide)
          have hre : R%2=0 := by
            dsimp [R]
            rw [Int.pow_succ, Int.mul_emod]
            simp
          have hnadd : (r+1)+((a+1)-(r+1))=a+1 := by omega
          have hpow : (2:Int)^(a+1)=R*z := by
            rw [←hnadd, Int.pow_add]
          have hmz : M=R*z+1 := by
            dsimp [M]
            rw [hpow]
          have hRle : R≤R*z := by
            have hmul := Int.mul_le_mul_of_nonneg_left (show (1:Int)≤z by omega)
              (show 0≤R by omega)
            simpa only [Int.mul_one] using hmul
          have hRlt : R<M := by omega
          have hh := generalized_gap_no_divisors c K M R z
            hc hk hkodd hre hrp hRlt hmz (by simpa only [M] using hstrong)
          exact hh
    · have hn_ge : a+1 ≤ n := by omega
      let t : Nat := n-(a+1)
      have ht : t<n := by dsimp [t]; omega
      have hn : n=(a+1)+t := by dsimp [t]; omega
      have hpow : c*(2:Int)^n+c*(2:Int)^t=M*(c*(2:Int)^t) := by
        rw [hn, Int.pow_add]
        dsimp [M]
        simp only [Int.add_mul]
        ac_rfl
      have hsum : M ∣ c*(2:Int)^n+c*(2:Int)^t := ⟨c*(2:Int)^t,hpow⟩
      obtain ⟨hnm,hnp⟩ := ih t ht
      exact flip_nondivisibility M K (c*(2:Int)^n) (c*(2:Int)^t) hsum hnm hnp
#print axioms no_power_signed_gap
end BB6Sheep17Gap
