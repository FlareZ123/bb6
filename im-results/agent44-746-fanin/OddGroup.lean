import FirstInverseComplete
import BandTriple
set_option maxHeartbeats 0
namespace CascadeAgent44
open CascadeResetInverse

private theorem pow_three_odd (b : Nat) : 3^b % 2 = 1 := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]

/-- A complete, valid odd first-reset inverse-band parameter at valuation t. -/
def OddParam (u t : Nat) : Prop :=
  ∃ k d, d%2=1 ∧
   (6*2^k+1 ≤ 2^t*d ∧ 2^t*d ≤ 8*2^k-1) ∧
   2*u+5=3^(t+1)*d

private theorem k_four_le (k : Nat) : k+4 ≤ 4*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    have hp : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
    omega

/-- Any valid odd valuation parameter yields an actual first-reset parent
    under the complete source-C reset semantics. -/
theorem odd_param_has_reset_parent (u t : Nat) (hp : OddParam u t) :
    ∃ h, ResetParent h u := by
  obtain ⟨k,d,hd,hband,hout⟩ := hp
  let q := 2^t*d
  let h := 2*q - 8*2^k-k-5
  have hk := k_four_le k
  have hlarge : 8*2^k+k+5 ≤ 2*q := by
    dsimp [q]
    omega
  have heq : 2*q=8*2^k+h+k+5 := by
    dsimp [h]
    omega
  refine ⟨h,Or.inr ⟨k,t,d,hd,hband,hout,?_⟩⟩
  dsimp [q] at heq
  exact heq

private theorem odd_param_scaled (u j e a b k : Nat)
  (hab : a+b=3)
  (he : e%2=1)
  (hz : 2*u+5=3^(3*j+4)*e)
  (hb : 6*2^k+1 ≤ (2^a*3^b)*(2^(3*j)*e) ∧
        (2^a*3^b)*(2^(3*j)*e) ≤ 8*2^k-1) :
  OddParam u (3*j+a) := by
  let d := 3^b*e
  have hd : d%2=1 := by
    have hs : (3^b)%2=1 := pow_three_odd b
    dsimp [d]
    rw [Nat.mul_mod,hs]
    omega
  have hq : 2^(3*j+a)*d=(2^a*3^b)*(2^(3*j)*e) := by
    dsimp [d]
    rw [Nat.pow_add]
    ac_rfl
  have hf : 3^((3*j+a)+1)*d = 3^(3*j+4)*e := by
    dsimp [d]
    rw [←Nat.mul_assoc, ←Nat.pow_add]
    have heqExp : 3*j+a+1+b=3*j+4 := by omega
    rw [heqExp]
  exact ⟨k,d,hd,(by simpa [hq] using hb), (by rw [hf];exact hz)⟩

/-- Exact 3-adic input at any valuation depth enforces a nontrivial odd
    inverse branch in every block of three successive valuations. -/
theorem three_consecutive_params (u j e : Nat)
    (he : e%2=1)
    (hz : 2*u+5=3^(3*j+4)*e) :
    ∃ t, 3*j ≤ t ∧ t ≤ 3*j+2 ∧ OddParam u t := by
  let v := 2^(3*j)*e
  have hv : 0 < v := by
    dsimp [v]
    have hp : 0 < 2^(3*j) := Nat.one_le_pow (3*j) 2 (by decide)
    have hepos : 0 < e := by omega
    exact Nat.mul_pos hp hepos
  rcases three_odd_bands v hv with h12 | h18 | h27
  · obtain ⟨k,hk,hl,hu⟩ := h12
    refine ⟨3*j+2,by omega,by omega,?_⟩
    apply odd_param_scaled u j e 2 1 k (by decide) he hz
    exact ⟨hl,hu⟩
  · obtain ⟨k,hk,hl,hu⟩ := h18
    refine ⟨3*j+1,by omega,by omega,?_⟩
    apply odd_param_scaled u j e 1 2 k (by decide) he hz
    exact ⟨hl,hu⟩
  · obtain ⟨k,hk,hl,hu⟩ := h27
    refine ⟨3*j,by omega,by omega,?_⟩
    apply odd_param_scaled u j e 0 3 k (by decide) he hz
    exact ⟨hl,hu⟩

#print axioms three_consecutive_params
#print axioms odd_param_has_reset_parent
end CascadeAgent44

namespace CascadeAgent44

/-- No search is needed: valuation divisibility of a target creates a genuine
    odd reset-parameter witness within the indicated three-level block. -/
theorem three_consecutive_of_divisible (u j : Nat)
    (hmod : (2*u+5)%3^(3*j+4)=0) :
    ∃ t, 3*j ≤ t ∧ t ≤ 3*j+2 ∧ OddParam u t := by
  let e := (2*u+5)/3^(3*j+4)
  have hz : 2*u+5=3^(3*j+4)*e := by
    have hm := Nat.mod_add_div (2*u+5) (3^(3*j+4))
    dsimp [e]
    omega
  have he : e%2=1 := by
    have hzodd : (2*u+5)%2=1 := by omega
    rw [hz,Nat.mul_mod,pow_three_odd] at hzodd
    omega
  exact three_consecutive_params u j e he hz

/-- Every full block of three 3-adic valuation positions contains at least
    one valid odd first-reset inverse parameter, uniformly at arbitrary height. -/
theorem every_three_odd_params (u M : Nat)
    (hmod : (2*u+5)%3^(3*M+1)=0) :
    ∀ j, j<M → ∃ t, 3*j ≤ t ∧ t ≤ 3*j+2 ∧ OddParam u t := by
  intro j hj
  have he : 3*j+4 ≤ 3*M+1 := by omega
  have hd : 3^(3*j+4) ∣ (2*u+5) :=
    Nat.dvd_trans (Nat.pow_dvd_pow 3 he) (Nat.dvd_of_mod_eq_zero hmod)
  exact three_consecutive_of_divisible u j (Nat.mod_eq_zero_of_dvd hd)

#print axioms three_consecutive_of_divisible
#print axioms every_three_odd_params
end CascadeAgent44
