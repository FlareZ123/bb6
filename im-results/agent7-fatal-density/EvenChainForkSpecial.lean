import EvenChainFork
set_option maxHeartbeats 0
namespace CascadeEvenChainForkSpecial
open CascadeFiveForced CascadeOddRay CascadeResetInverse CascadeSweep
open CascadeEvenChainFork CascadeForkOddDead27

private theorem odd_band_unique (u k l:Nat)
  (hk:6*2^k+1≤u ∧ u≤8*2^k-1)
  (hl:6*2^l+1≤u ∧ u≤8*2^l-1):k=l:=by
  by_cases he:k=l
  · exact he
  by_cases hklt:k<l
  · have hp:2^(k+1)≤2^l:=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega
  · have hp:2^(l+1)≤2^k:=
      Nat.pow_le_pow_right (by decide:0<(2:Nat)) (by omega)
    rw[Nat.pow_succ] at hp
    omega

/-- A concrete entire exact odd fork at ray depth 16, index n=28, is
    root-inaccessible. The underlying genuine source arithmetic admits
    t=1, but its physical parent h is excluded by the new two-step gap
    certificate; t=0,2 are in odd-image dyadic gaps and t>=3 contradicts
    the exact 3-adic valuation of 2*ray(28,16)+5. The full even
    continuation of the canonical ray remains explicitly unclassified. -/
theorem ray28_depth16_odd_root_absent : ¬oddRootAt 28 16 := by
  rintro ⟨q,hroot,⟨k,t,d,hd,hband,hout,heq⟩⟩
  have hv:ray 28 16=1069875227:=by decide
  rw[hv] at hout
  by_cases ht0:t=0
  · subst t
    have h3:2139750459=3*d:=by simpa using hout
    have hdval:d=713250153:=by omega
    have hgap:2^29<d ∧ 2*d+2<3*2^29:=by
      rw[hdval]
      decide
    have hband0:6*2^k+1≤d ∧ d≤8*2^k-1:=by
      simpa using hband
    exact ((gap_avoids_odd_images 29 d hgap.1 hgap.2) k hband0).elim
  by_cases ht1:t=1
  · subst t
    have h9:2139750459=9*d:=by simpa using hout
    have hdval:d=237750051:=by omega
    have hband1:6*2^k+1≤2*d ∧ 2*d≤8*2^k-1:=by
      simpa using hband
    have hb26:6*2^26+1≤2*d ∧ 2*d≤8*2^26-1:=by
      rw[hdval]
      decide
    have hk:k=26:=odd_band_unique (2*d) k 26 hband1 hb26
    have hp26:2^26=67108864:=by decide
    have hqval:q=414129261:=by
      rw[hk,hdval,hp26] at heq
      simp only [show (2:Nat)^1=2 by decide] at heq
      omega
    rw[hqval] at hroot
    exact offray_28_16_unreachable hroot
  by_cases ht2:t=2
  · subst t
    have h27:2139750459=27*d:=by simpa using hout
    have hdval:d=79250017:=by omega
    have hgap:2^28<4*d ∧ 2*(4*d)+2<3*2^28:=by
      rw[hdval]
      decide
    have hband2:6*2^k+1≤4*d ∧ 4*d≤8*2^k-1:=by
      simpa using hband
    exact ((gap_avoids_odd_images 28 (4*d) hgap.1 hgap.2) k hband2).elim
  have ht3:3≤t:=by omega
  have hex:t+1=4+(t-3):=by omega
  have hpow:3^(t+1)=81*3^(t-3):=by
    rw[hex,Nat.pow_add]
    simp only [show (3:Nat)^4=81 by decide]
  have hmod:(3^(t+1)*d)%81=0:=by
    rw[hpow]
    simp [Nat.mul_mod]
  have hnot:2139750459%81≠0:=by decide
  have hmod2:2139750459%81=0:=by rw[hout];exact hmod
  exact hnot hmod2

#print axioms ray28_depth16_odd_root_absent
end CascadeEvenChainForkSpecial
