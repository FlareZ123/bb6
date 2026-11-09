import MiddleLowOddGap

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse

/-- The mod-nine condition for odd parents in the middle-low band is
    sufficient as well as necessary. The explicit witness has odd
    valuation t=1 and source sweep exponent j=k−2. -/
theorem middle_low_odd_has_parent (h k : Nat)
    (hk : 2≤k)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k)
    (hdiv : (2*h+5)%9=0) :
    ∃a, (a+firstFailIndex a)%2=1 ∧ bitOutcome a=some h := by
  let j := k-2
  let d := (2*h+5)/9
  let q := 2*d
  let a := 2*q-8*2^j-j-5
  have hj : j+2=k := by dsimp [j]; omega
  have hpow : 2^k=4*2^j := by
    rw [←hj,show j+2=(j+1)+1 by omega,Nat.pow_succ,Nat.pow_succ]
    omega
  have hdn : 9*d=2*h+5 := by dsimp [d]; omega
  have hodd : d%2=1 := by omega
  have hq9 : 9*q=4*h+10 := by dsimp [q]; omega
  have hb1 : 6*2^j+1≤q := by omega
  have hb2 : q≤8*2^j-1 := by omega
  have hlinear : j+4≤4*2^j := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hlarge : 8*2^j+j+5≤2*q := by omega
  have heq : 2*q=8*2^j+a+j+5 := by dsimp [a]; omega
  have hlowIndex : 4*2^j≤a+j+4 := by omega
  have hhigh : a+j+5<8*2^j := by omega
  have hindex : firstFailIndex a=j :=
    firstFailIndex_unique a j hhigh
      (guards_from_low a j hlowIndex)
  have hpar : (a+firstFailIndex a)%2=1 := by
    rw [hindex]
    omega
  have heqout : 2*h+5=3^(1+1)*d := by
    have hn : 3^(1+1)=9 := by decide
    rw [hn]
    omega
  have hparent : CascadeResetInverse.ResetParent a h :=
    Or.inr ⟨j,1,d,hodd,⟨hb1,hb2⟩,heqout,heq⟩
  have hr := reset_parent_sufficient a h hparent
  have hb := bitOutcome_sound a
  exact ⟨a,hpar,outcome_unique hb hr⟩

/-- Exact image classification for every lower-middle target at
    an arbitrary dyadic level k. This is a source first-reset
    equivalence, with no assertion of authentic blank reachability. -/
theorem middle_low_odd_image_iff (h k : Nat)
    (hk : 2≤k)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k) :
    (∃a, (a+firstFailIndex a)%2=1 ∧ bitOutcome a=some h) ↔
      (2*h+5)%9=0 := by
  constructor
  · rintro ⟨a,hpar,ho⟩
    exact middle_low_odd_output_mod_nine a h k hpar ho hlow htop
  · exact middle_low_odd_has_parent h k hk hlow htop

#print axioms middle_low_odd_has_parent
#print axioms middle_low_odd_image_iff

/-- Complete (even or odd) original first-reset image in the lower-middle
    dyadic strip: there is a source reset parent exactly at the ONE residue
    class h ≡ 2 (mod 9). The even source image has a dyadic gap here. -/
theorem middle_low_full_image_iff (h k : Nat)
    (hk : 3≤k)
    (hlow : 4*2^k≤h)
    (htop : 2*h+5<9*2^k) :
    (∃a, bitOutcome a=some h) ↔ h%9=2 := by
  have hmin : 4*2^k-3<h := by omega
  have hmax : h<6*2^k-1 := by omega
  have hgap : ∀ j, ¬(6*2^j-1≤h ∧ h≤8*2^j-3) := by
    intro j
    have hshift : (k+1)-1=k := by omega
    exact TerminalExit.no_even_band (k+1) j h
      (by omega) (by simpa [hshift] using hmin)
      (by simpa [hshift] using hmax)
  constructor
  · rintro ⟨a,ho⟩
    have hr := bitOutcome_sound a
    rw [ho] at hr
    have hp := reset_parent_necessary a h hr
    rcases hp with ⟨j,hband,heq⟩ | ⟨j,t,d,hd,hband,hout,hq⟩
    · exact False.elim (hgap j hband)
    · have hlowIndex : 4*2^j≤a+j+4 := by omega
      have hhigh : a+j+5<8*2^j := by omega
      have hindex : firstFailIndex a=j :=
        firstFailIndex_unique a j hhigh
          (guards_from_low a j hlowIndex)
      have hpar : (a+firstFailIndex a)%2=1 := by
        rw [hindex]
        omega
      have hdiv := middle_low_odd_output_mod_nine a h k
        hpar ho hlow htop
      omega
  · intro hres
    have hdiv : (2*h+5)%9=0 := by omega
    obtain ⟨a,_,hout⟩ :=
      middle_low_odd_has_parent h k (by omega) hlow htop hdiv
    exact ⟨a,hout⟩

#print axioms middle_low_full_image_iff
end CascadeFastReturn
