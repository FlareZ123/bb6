import FeederSixArithmetic
set_option maxHeartbeats 0

namespace CascadeFeederExceptional
open CascadeSweep CascadeResetInverse CascadeFastReturn CascadeUniformFatal
open CascadeAncestry CascadeFirstFork CascadeManyShield

private theorem odd_gap (k v : Nat) (hlo : 2*2^k < v)
    (hhi : v < 3*2^k) :
    ∀j, ¬(6*2^j+1≤v ∧ v≤8*2^j-1) := by
  intro j hb
  by_cases hj : j+2≤k
  · have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj
    have he : 2^(j+2)=4*2^j := by rw [Nat.pow_add]; omega
    rw [he] at hp
    omega
  · have hj' : k≤j+1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hj'
    have he : 2^(j+1)=2*2^j := by rw [Nat.pow_succ]; omega
    rw [he] at hp
    omega

private theorem no_even_band_from_gap (k u : Nat)
    (hlo : 4*2^k-3 < u) (hhi : u < 6*2^k-1) :
    ∀j, ¬(6*2^j-1≤u ∧ u≤8*2^j-3) := by
  intro j
  have hshift : (k+1)-1=k := by omega
  apply TerminalExit.no_even_band (k+1) j u
  · omega
  · simpa [hshift] using hlo
  · simpa [hshift] using hhi

private theorem even_backward (u v j : Nat)
    (hb : 6*2^j-1≤u ∧ u≤8*2^j-3)
    (he : 2*u=8*2^j+v+j)
    (hm : u%3≠2)
    (hr : ReachC (2,0) (u,0)) :
    ReachC (2,0) (v,0) := by
  obtain ⟨q,m,hqr,hlo,hhi,heq⟩ :=
    reachable_even_reset_parent u hr hm
  have hindex : m=j := even_band_unique u m j ⟨hlo,hhi⟩ hb
  rw [hindex] at heq
  have hqv : q=v := by omega
  simpa [hqv] using hqr

private theorem parent_backward (u v : Nat)
    (hne : u≠2)
    (huniq : ∀q, ResetParent q u → q=v)
    (hr : ReachC (2,0) (u,0)) :
    ReachC (2,0) (v,0) := by
  have hc : ResetChain 2 u := (root_reset_chain_iff u).mp hr
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc hne
  have hqv : q=v := huniq q hq
  rw [hqv] at hqc
  exact (root_reset_chain_iff v).mpr hqc

/-- A target in an even image band whose only possible odd quotient lies
    in a dyadic gap has exactly its displayed even first-reset parent. -/
private theorem only_even_parent_of_gap (u v j q : Nat)
    (hb : 6*2^j-1≤u ∧ u≤8*2^j-3)
    (he : 2*u=8*2^j+v+j)
    (hdiv3 : (2*u+5)%3=0)
    (hnot9 : (2*u+5)%9≠0)
    (hgap : 2*2^(j+1)<(2*u+5)/3 ∧
      (2*u+5)/3<3*2^(j+1))
    (hp : ResetParent q u) : q=v := by
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
  · have hindex : m=j := even_band_unique u m j hbm hb
    rw [hindex] at heq
    omega
  · have ht0 : t=0 := by
      by_cases ht : t=0
      · exact ht
      · have hpow : 9∣3^(t+1) :=
          Nat.pow_dvd_pow 3 (by omega : 2≤t+1)
        have hdiv : 9∣2*u+5 := by
          rw [hout]
          exact dvd_mul_of_dvd_left hpow d
        exact False.elim (hnot9 (Nat.mod_eq_zero_of_dvd hdiv))
    subst t
    have hdval : 3*d=2*u+5 := by simpa using hout.symm
    have hdq : d=(2*u+5)/3 := by omega
    have hgap' : 2*2^(j+1)<d ∧ d<3*2^(j+1) := by
      simpa [hdq] using hgap
    exact False.elim (odd_gap (j+1) d hgap'.1 hgap'.2 m hbm)

private theorem even_backward_gap (u v j : Nat)
    (hj : 1≤j)
    (hb : 6*2^j-1≤u ∧ u≤8*2^j-3)
    (he : 2*u=8*2^j+v+j)
    (hdiv3 : (2*u+5)%3=0)
    (hnot9 : (2*u+5)%9≠0)
    (hgap : 2*2^(j+1)<(2*u+5)/3 ∧
      (2*u+5)/3<3*2^(j+1))
    (hr : ReachC (2,0) (u,0)) :
    ReachC (2,0) (v,0) := by
  have huniq : ∀q, ResetParent q u → q=v :=
    fun q hp => only_even_parent_of_gap u v j q hb he hdiv3 hnot9 hgap hp
  have hpow : 0<2^j := Nat.pow_pos (by decide)
  have hne : u≠2 := by omega
  exact parent_backward u v hne huniq hr

/-- In the middle-low band, v3(2h+5)=3 forces the unique odd parent
    to have valuation exponent t=1; the t=0 and t=2 quotients are in
    adjacent dyadic gaps, while t>=3 contradicts 81-nondivisibility. -/
private theorem middle_low_unique_odd_t1 (h k a q : Nat)
    (hk : 3≤k)
    (hlo : 4*2^k≤h)
    (htop : 2*h+5<9*2^k)
    (hdiv27 : (2*h+5)%27=0)
    (hnodiv81 : (2*h+5)%81≠0)
    (ha : 4*((2*h+5)/9)=8*2^(k-2)+a+(k-2)+5)
    (hp : ResetParent q h) : q=a := by
  have hmin : 4*2^k-3<h := by omega
  have hmax : h<6*2^k-1 := by omega
  have hgap : ∀j, ¬(6*2^j-1≤h ∧ h≤8*2^j-3) :=
    no_even_band_from_gap k h hmin hmax
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
  · exact False.elim (hgap m hbm)
  · have htle : t≤2 := by
      by_cases ht : t≤2
      · exact ht
      · have hpow : 81∣3^(t+1) :=
          Nat.pow_dvd_pow 3 (by omega : 4≤t+1)
        have hdiv : 81∣2*h+5 := by
          rw [hout]
          exact dvd_mul_of_dvd_left hpow d
        exact False.elim (hnodiv81 (Nat.mod_eq_zero_of_dvd hdiv))
    by_cases ht0 : t=0
    · subst t
      have hdval : 3*d=2*h+5 := by simpa using hout.symm
      have hdq : d=(2*h+5)/3 := by omega
      have hqlo : 2*2^k<d := by rw [hdq]; omega
      have hqhi : d<3*2^k := by rw [hdq]; omega
      exact False.elim (odd_gap k d hqlo hqhi m hbm)
    · by_cases ht1 : t=1
      · subst t
        have h9 : 9*d=2*h+5 := by simpa using hout.symm
        have hdd : d=(2*h+5)/9 := by omega
        have hband : 6*2^(k-2)+1≤2*((2*h+5)/9) ∧
            2*((2*h+5)/9)≤8*2^(k-2)-1 := by
          rw [←hdd]
          omega
        have hj : m=k-2 :=
          CascadeFirstFork.odd_band_scale_unique
            (2*((2*h+5)/9)) m (k-2)
            (by simpa [hdd] using hbm) hband
        rw [hj,hdd] at hq
        omega
      · have ht2 : t=2 := by omega
        subst t
        have h27 : 27*d=2*h+5 := by simpa using hout.symm
        have hdq : d=(2*h+5)/27 := by omega
        have hqlo : 2*2^(k-1)<4*d := by rw [hdq]; omega
        have hqhi : 4*d<3*2^(k-1) := by rw [hdq]; omega
        exact False.elim (odd_gap (k-1) (4*d) hqlo hqhi m hbm)

/-- In a middle-low gap, if v3(2u+5)=1 and its t=0 odd quotient is
    in a specified odd image band, that odd parent is unique. -/
private theorem middle_low_unique_odd_t0 (u j f q : Nat)
    (hlo : 4*2^j≤u)
    (hhi : u<6*2^j-1)
    (hdiv3 : (2*u+5)%3=0)
    (hnot9 : (2*u+5)%9≠0)
    (hband : 6*2^(j-1)+1≤(2*u+5)/3 ∧
      (2*u+5)/3≤8*2^(j-1)-1)
    (hf : 2*((2*u+5)/3)=8*2^(j-1)+f+(j-1)+5)
    (hp : ResetParent q u) : q=f := by
  have hgap : ∀m, ¬(6*2^m-1≤u ∧ u≤8*2^m-3) :=
    no_even_band_from_gap j u (by omega) hhi
  rcases hp with ⟨m,hbm,heq⟩ | ⟨m,t,d,hdodd,hbm,hout,hq⟩
  · exact False.elim (hgap m hbm)
  · have ht0 : t=0 := by
      by_contra ht
      have hpow : 9∣3^(t+1) :=
        Nat.pow_dvd_pow 3 (by omega : 2≤t+1)
      have hdiv : 9∣2*u+5 := by
        rw [hout]
        exact dvd_mul_of_dvd_left hpow d
      exact hnot9 (Nat.mod_eq_zero_of_dvd hdiv)
    subst t
    have hdval : 3*d=2*u+5 := by simpa using hout.symm
    have hdd : d=(2*u+5)/3 := by omega
    have hj : m=j-1 :=
      CascadeFirstFork.odd_band_scale_unique
        ((2*u+5)/3) m (j-1)
        (by simpa [hdd] using hbm) hband
    rw [hj,hdd] at hq
    omega

/-- Two exceptional 1458-adic classes of the t=1 fatal odd feeder are
    excluded by a seven-edge exact inverse chain: even, odd-t1, four
    forced evens, then odd-t0 into a final no-parent gap. -/
theorem seven_stage_root_exclusion
    (k j x h a b c d e f : Nat)
    (hk : 3≤k)
    (hj : 1≤j)
    (hkj : j+2=k)
    (hxband : 6*2^k-1≤x ∧ x≤8*2^k-3)
    (hxeq : 2*x=8*2^k+h+k)
    (hxmod : x%3≠2)
    (hhlo : 4*2^k≤h)
    (hhtop : 2*h+5<9*2^k)
    (hh27 : (2*h+5)%27=0)
    (hh81 : (2*h+5)%81≠0)
    (haodd : 4*((2*h+5)/9)=8*2^j+a+j+5)
    (haBand : 6*2^j-1≤a ∧ a≤8*2^j-3)
    (hbBand : 6*2^j-1≤b ∧ b≤8*2^j-3)
    (hcBand : 6*2^j-1≤c ∧ c≤8*2^j-3)
    (hdBand : 6*2^j-1≤d ∧ d≤8*2^j-3)
    (hab : 2*a=8*2^j+b+j)
    (hbc : 2*b=8*2^j+c+j)
    (hcd : 2*c=8*2^j+d+j)
    (hde : 2*d=8*2^j+e+j)
    (haDiv3 : (2*a+5)%3=0)
    (hbDiv3 : (2*b+5)%3=0)
    (hcDiv3 : (2*c+5)%3=0)
    (hdDiv3 : (2*d+5)%3=0)
    (haNot9 : (2*a+5)%9≠0)
    (hbNot9 : (2*b+5)%9≠0)
    (hcNot9 : (2*c+5)%9≠0)
    (hdNot9 : (2*d+5)%9≠0)
    (haGap : 2*2^(j+1)<(2*a+5)/3 ∧ (2*a+5)/3<3*2^(j+1))
    (hbGap : 2*2^(j+1)<(2*b+5)/3 ∧ (2*b+5)/3<3*2^(j+1))
    (hcGap : 2*2^(j+1)<(2*c+5)/3 ∧ (2*c+5)/3<3*2^(j+1))
    (hdGap : 2*2^(j+1)<(2*d+5)/3 ∧ (2*d+5)/3<3*2^(j+1))
    (heLo : 4*2^j≤e)
    (heHi : e<6*2^j-1)
    (heDiv3 : (2*e+5)%3=0)
    (heNot9 : (2*e+5)%9≠0)
    (heBand : 6*2^(j-1)+1≤(2*e+5)/3 ∧
      (2*e+5)/3≤8*2^(j-1)-1)
    (hfEq : 2*((2*e+5)/3)=8*2^(j-1)+f+(j-1)+5)
    (hfGapLo : 4*2^(j-1)-3<f)
    (hfGapHi : f<6*2^(j-1)-1)
    (hfmod : f%3≠2) :
    ¬ReachC (2,0) (x,0) := by
  have hpowk : 0<2^k := Nat.pow_pos (by decide)
  have hpowj : 0<2^j := Nat.pow_pos (by decide)
  have hNoF : ¬ReachC (2,0) (f,0) :=
    root_excludes_nonimage f hfmod
      (no_even_band_from_gap (j-1) f hfGapLo hfGapHi)
  intro hr
  have hH : ReachC (2,0) (h,0) :=
    even_backward x h k hxband hxeq hxmod hr
  have hA : ReachC (2,0) (a,0) :=
    parent_backward h a (by omega)
      (fun q hp => middle_low_unique_odd_t1 h k a q hk
        hhlo hhtop hh27 hh81 (by
        have hkm : k-2=j := by omega
        simpa [hkm] using haodd) hp) hH
  have hB : ReachC (2,0) (b,0) :=
    even_backward_gap a b j hj haBand hab haDiv3 haNot9 haGap hA
  have hC : ReachC (2,0) (c,0) :=
    even_backward_gap b c j hj hbBand hbc hbDiv3 hbNot9 hbGap hB
  have hD : ReachC (2,0) (d,0) :=
    even_backward_gap c d j hj hcBand hcd hcDiv3 hcNot9 hcGap hC
  have hE : ReachC (2,0) (e,0) :=
    even_backward_gap d e j hj hdBand hde hdDiv3 hdNot9 hdGap hD
  have hF : ReachC (2,0) (f,0) :=
    parent_backward e f (by omega)
      (fun q hp => middle_low_unique_odd_t0 e j f q heLo heHi heDiv3 heNot9 heBand hfEq hp)
      hE
  exact hNoF hF

end CascadeFeederExceptional
