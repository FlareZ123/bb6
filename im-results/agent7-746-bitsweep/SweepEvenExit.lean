import SweepEvenOrbit

namespace CascadeFastReturn
open CascadeBitSweep

/-- A short even deficit near the upper guard forces a strict dyadic-level advance. -/
theorem even_boundary_advances (k d : Nat)
    (hdlo : 2*k+6 ≤ d)
    (hdhi : d < 4*k+12)
    (heven : d%2=0)
    (hlo : 4*2^k ≤ atHeight k 0 d) :
    let h := atHeight k 0 d
    let u := 8*2^k+k-d/2
    bitOutcome h = some u ∧ k < firstFailIndex u := by
  dsimp only
  let p := 2^k
  let a := 8*p+k
  let h := atHeight k 0 d
  let u := a-d/2
  have hp : 1≤p := Nat.one_le_pow k 2 (by decide)
  have hhlo : 4*p≤h := hlo
  have hbound : d≤a := by
    dsimp [h,atHeight] at hhlo
    omega
  have hrepr : h+d=a := by
    dsimp [h,atHeight,a,p]
    simpa using Nat.sub_add_cancel hbound
  have urepr : u+d/2=a := by
    dsimp [u]
    exact Nat.sub_add_cancel (by omega)
  have huLow : 4*p ≤ u := by omega
  have hguard : h+k+5<8*p := by omega
  have hbefore (j : Nat) (hj:j<k) : 8*2^j ≤ h+j+5 := by
    have hpow : 8*2^j ≤4*p := by
      dsimp [p]
      have hp8 : 8*2^j=2^(j+3) := by rw [Nat.pow_add]; simp [Nat.mul_comm]
      have hp4 : 4*2^k=2^(k+2) := by rw [Nat.pow_add]; simp [Nat.mul_comm]
      rw [hp8,hp4]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hk : firstFailIndex h=k := firstFailIndex_unique h k (by simpa only [p] using hguard) hbefore
  have hpar : (h+k)%2=0 := by omega
  have hfat : h+k+4≠4*2^k := by omega
  have hquot : (h+k)/2=u-4*p := by omega
  have he : bitOutcome h=some u := by
    simp only [bitOutcome, hk, hfat, hpar, ↓reduceIte]
    congr 1
    omega
  have hmono : h≤u := by omega
  have hclear : 8*2^k≤u+k+5 := by omega
  exact ⟨he,firstFailIndex_advance h u k hk hmono hclear⟩

#print axioms even_boundary_advances
end CascadeFastReturn
