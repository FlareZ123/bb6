import MiddleLowOddExact
import ResetAncestry
import FirstForkExactTwo
set_option maxHeartbeats 0
namespace CascadeFeederSix
open CascadeSweep CascadeResetInverse CascadeFastReturn CascadeUniformFatal CascadeAncestry

private theorem pow_shift_two (k : Nat) (hk : 2 ≤ k) :
    2^k=4*2^(k-2) := by
  have ht : k=(k-2)+2 := by omega
  calc
    2^k = 2^((k-2)+2) := congrArg (fun j : Nat => 2^j) ht
    _ = 2^(k-2)*4 := by rw [Nat.pow_add]
    _ = 4*2^(k-2) := by omega

/-- The odd quotient bands avoid the open dyadic gap (2P,3P). -/
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

private theorem middle_low_unique_odd (h k a q : Nat)
    (hk : 3≤k)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k)
    (hdiv9 : (2*h+5)%9=0)
    (hnodiv27 : (2*h+5)%27≠0)
    (ha : 4*((2*h+5)/9)=8*2^(k-2)+a+(k-2)+5)
    (hp : ResetParent q h) : q=a := by
  have hpow : 2^k=4*2^(k-2) := pow_shift_two k (by omega)
  have hd : 9*((2*h+5)/9)=2*h+5 := by omega
  have hmin : 4*2^k-3<h := by omega
  have hmax : h<6*2^k-1 := by omega
  have hgap : ∀j, ¬(6*2^j-1≤h ∧ h≤8*2^j-3) := by
    intro j
    have hshift : (k+1)-1=k := by omega
    exact TerminalExit.no_even_band (k+1) j h
      (by omega) (by simpa [hshift] using hmin)
      (by simpa [hshift] using hmax)
  rcases hp with ⟨j,hbj,heqj⟩ | ⟨j,t,d,hdodd,hbj,hout,hq⟩
  · exact False.elim (hgap j hbj)
  · by_cases ht0 : t=0
    · subst t
      have hq3 : 3*d=2*h+5 := by simpa using hout.symm
      have qlo : 2*2^k<d := by omega
      have qhi : d<3*2^k := by omega
      exact False.elim (odd_gap k d qlo qhi j (by simpa using hbj))
    · by_cases ht1 : t=1
      · subst t
        have hq9 : 9*d=2*h+5 := by simpa using hout.symm
        have hdd : d=(2*h+5)/9 := by omega
        have hband : 6*2^(k-2)+1≤2*((2*h+5)/9) ∧
            2*((2*h+5)/9)≤8*2^(k-2)-1 := by
          omega
        have hj : j=k-2 := CascadeFirstFork.odd_band_scale_unique
           (2*((2*h+5)/9)) j (k-2)
           (by simpa [hdd] using hbj) hband
        rw [hj, hdd] at hq
        omega
      · have ht2 : 2≤t := by omega
        have hpower : 27 ∣ 3^(t+1) := by
          exact Nat.pow_dvd_pow 3 (by omega : 3≤t+1)
        have hdiv : 27 ∣ 2*h+5 := by
          rw [hout]
          obtain ⟨z,hz⟩ := hpower
          exact ⟨z*d, by rw [hz]; ac_rfl⟩
        exact False.elim (hnodiv27 (Nat.mod_eq_zero_of_dvd hdiv))

/-- Source-exact unique even predecessor, lifted to the authentic root. -/
private theorem even_backward (v w j : Nat)
    (hb : 6*2^j-1≤v ∧ v≤8*2^j-3)
    (he : 2*v=8*2^j+w+j)
    (hm : v%3≠2)
    (hr : ReachC (2,0) (v,0)) : ReachC (2,0) (w,0) := by
  obtain ⟨q,m,hqr,hlo,hhi,heq⟩ :=
    reachable_even_reset_parent v hr hm
  have hindex : m=j := even_band_unique v m j ⟨hlo,hhi⟩ hb
  rw [hindex] at heq
  have hqw : q=w := by omega
  simpa [hqw] using hqr

private theorem odd_backward (h a : Nat)
    (hne : h≠2)
    (huniq : ∀q, ResetParent q h → q=a)
    (hr : ReachC (2,0) (h,0)) : ReachC (2,0) (a,0) := by
  have hc : ResetChain 2 h := (root_reset_chain_iff h).mp hr
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc hne
  have hqa : q=a := huniq q hq
  rw [hqa] at hqc
  exact (root_reset_chain_iff a).mpr hqc

/-- A two-stage feeder obstruction, followed by four forced even
    predecessors and a final nonimage. The precise hypotheses can be
    checked by affine families and modular arithmetic. -/
theorem six_stage_root_exclusion
 (k x h a b c d e : Nat)
 (hk : 5≤k)
 (hxband : 6*2^k-1≤x ∧ x≤8*2^k-3)
 (hxeq : 2*x=8*2^k+h+k)
 (hxmod : x%3≠2)
 (hlo : 4*2^k≤h)
 (hhi : 2*h+5<9*2^k)
 (h9 : (2*h+5)%9=0)
 (h27 : (2*h+5)%27≠0)
 (ha : 4*((2*h+5)/9)=8*2^(k-2)+a+(k-2)+5)
 (haBand : 6*2^(k-2)-1≤a ∧ a≤8*2^(k-2)-3)
 (hbBand : 6*2^(k-2)-1≤b ∧ b≤8*2^(k-2)-3)
 (hcBand : 6*2^(k-2)-1≤c ∧ c≤8*2^(k-2)-3)
 (hdBand : 6*2^(k-2)-1≤d ∧ d≤8*2^(k-2)-3)
 (hab : 2*a=8*2^(k-2)+b+(k-2))
 (hbc : 2*b=8*2^(k-2)+c+(k-2))
 (hcd : 2*c=8*2^(k-2)+d+(k-2))
 (hde : 2*d=8*2^(k-2)+e+(k-2))
 (ham : a%3≠2) (hbm : b%3≠2) (hcm : c%3≠2)
 (hdm : d%3≠2) (hem : e%3≠2)
 (heLower : 4*2^(k-2)≤e)
 (heUpper : e<6*2^(k-2)-1) :
 ¬ReachC (2,0) (x,0) := by
  have heGap : ∀j, ¬(6*2^j-1≤e ∧ e≤8*2^j-3) := by
    intro j
    have hshift : ((k-2)+1)-1=k-2 := by omega
    apply TerminalExit.no_even_band ((k-2)+1) j e
    · omega
    · simpa [hshift] using (show 4*2^(k-2)-3<e by omega)
    · simpa [hshift] using heUpper
  have heNo : ¬ReachC (2,0) (e,0) :=
    root_excludes_nonimage e hem heGap
  intro hr
  have hhr := even_backward x h k hxband hxeq hxmod hr
  have hha : ReachC (2,0) (a,0) :=
    odd_backward h a (by omega)
      (fun q hp => middle_low_unique_odd h k a q (by omega)
        hlo hhi h9 h27 ha hp) hhr
  have hhb := even_backward a b (k-2) haBand hab ham hha
  have hhc := even_backward b c (k-2) hbBand hbc hbm hhb
  have hhd := even_backward c d (k-2) hcBand hcd hcm hhc
  have hhe := even_backward d e (k-2) hdBand hde hdm hhd
  exact heNo hhe

#print axioms middle_low_unique_odd
#print axioms six_stage_root_exclusion
end CascadeFeederSix
