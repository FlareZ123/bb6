import SweepBitLength

namespace CascadeBitSweep

def atHeight (k m d : Nat) : Nat := 8*2^k+k-2^m*d

/-- Exact one-step even return on a whole dyadic-addressed family. -/
theorem even_block_one (k m d : Nat)
    (hd : 2*k+6 ≤ d)
    (hlo : 4*2^k ≤ atHeight k (m+1) d) :
    let h := atHeight k (m+1) d
    let u := atHeight k m d
    firstFailIndex h=k ∧ (h+k)%2=0 ∧ 4*2^k+(h+k)/2=u := by
  dsimp only
  let p := 2^k
  let z := 2^m*d
  let a := 8*p+k
  let h := atHeight k (m+1) d
  let u := atHeight k m d
  have hz : 2^(m+1)*d=2*z := by
    simp [z, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
  have hrepr : h=a-2*z := by
    dsimp [h,a,p,atHeight]
    rw [hz]
  have urepr : u=a-z := rfl
  have hlow : 4*p≤h := hlo
  have ppositive : 1≤p := Nat.one_le_pow k 2 (by decide)
  have hbound : 2*z ≤ a := by
    rw [hrepr] at hlow
    omega
  have heq : h+2*z=a := by
    rw [hrepr]
    exact Nat.sub_add_cancel hbound
  have hu : u+z=a := by
    rw [urepr]
    exact Nat.sub_add_cancel (by omega)
  have huLow : 4*p≤u := by omega
  have hzLower : d ≤ z := by
    have hp : 1≤2^m := Nat.one_le_pow m 2 (by decide)
    simpa [z] using Nat.mul_le_mul_right d hp
  have hfirst : h+k+5 < 8*p := by omega
  have hbefore (j : Nat) (hj : j<k) : 8*2^j ≤ h+j+5 := by
    have hpow : 8*2^j≤4*p := by
      dsimp [p]
      have he : 8*2^j=2^(j+3) := by rw [Nat.pow_add]; simp [Nat.mul_comm]
      have he2 : 4*2^k=2^(k+2) := by rw [Nat.pow_add]; simp [Nat.mul_comm]
      rw [he,he2]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hk : firstFailIndex h=k := firstFailIndex_unique h k (by simpa only [p] using hfirst) hbefore
  have hpair : h+k=2*(u-4*p) := by omega
  have hpar : (h+k)%2=0 := by omega
  have hquot : (h+k)/2=u-4*p := by omega
  change firstFailIndex h=k ∧ (h+k)%2=0 ∧ 4*p+(h+k)/2=u
  refine ⟨hk,hpar,?_⟩
  omega

#print axioms even_block_one
end CascadeBitSweep
