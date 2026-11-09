import SweepOddFatal27Band

namespace CascadeFastReturn
open CascadeBitSweep

/-- Above the narrow cutoff, the exact high-band odd predecessor grammar
    has a valuation-one witness whenever its necessary modulo-nine condition
    holds. The quotient lies inside the dyadic band at index k-1. -/
theorem upper_high_odd_has_parent (entry k : Nat)
    (hk : 2≤k)
    (hlevel : firstFailIndex entry=k)
    (hupper : 27*2^k≤4*entry+10)
    (hdiv : (2*entry+5)%9=0) :
    ∃a, (a+firstFailIndex a)%2=1 ∧ bitOutcome a=some entry := by
  let j := k-1
  let d := (2*entry+5)/9
  let q := 2*d
  let a := 2*q-8*2^j-j-5
  have hj : j+1=k := by dsimp [j]; omega
  have hpow : 2^k=2*2^j := by rw [←hj,Nat.pow_succ]; omega
  have hpdiv4 : (2^k)%4=0 := by
    have hdiv4 : 2^2∣2^k := Nat.pow_dvd_pow 2 hk
    simpa using Nat.mod_eq_zero_of_dvd hdiv4
  have hdn : 9*d=2*entry+5 := by dsimp [d]; omega
  have hodd : d%2=1 := by omega
  have hq9 : 9*q=4*entry+10 := by dsimp [q]; omega
  have hl : 6*2^j+1≤q := by omega
  have hentryupper := (firstFailIndex_spec entry).2
  rw [hlevel] at hentryupper
  have hh : q≤8*2^j-1 := by omega
  have hlinear : j+4≤4*2^j := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hlarge : 8*2^j+j+5≤2*q := by omega
  have heq : 2*q=8*2^j+a+j+5 := by dsimp [a]; omega
  have hlow : 4*2^j≤a+j+4 := by omega
  have hhigh' : a+j+5<8*2^j := by omega
  have hindex : firstFailIndex a=j :=
    firstFailIndex_unique a j hhigh'
      (CascadeResetInverse.guards_from_low a j hlow)
  have hpar : (a+firstFailIndex a)%2=1 := by
    rw [hindex]
    omega
  have heqout : 2*entry+5=3^(1+1)*d := by
    have hn : 3^(1+1)=9 := by decide
    rw [hn]
    omega
  have hparent : CascadeResetInverse.ResetParent a entry :=
    Or.inr ⟨j,1,d,hodd,⟨hl,hh⟩,heqout,heq⟩
  have hr := CascadeResetInverse.reset_parent_sufficient a entry hparent
  have hb := bitOutcome_sound a
  exact ⟨a,hpar,CascadeResetInverse.outcome_unique hb hr⟩

/-- Complete exact high-band odd source image criterion. The narrow
    part requires 27-divisibility; the upper part requires nine-divisibility.
    No root reachability is claimed for any source predecessor. -/
theorem entire_high_odd_image_iff (entry k : Nat)
    (hlevel : firstFailIndex entry=k)
    (hk : 2≤k)
    (hlower : 6*2^k≤entry) :
    (∃a, (a+firstFailIndex a)%2=1 ∧ bitOutcome a=some entry) ↔
      (if 4*entry+10<27*2^k then (2*entry+5)%27=0
       else (2*entry+5)%9=0) := by
  by_cases hnarrow : 4*entry+10<27*2^k
  · simp only [if_pos hnarrow]
    exact narrow_high_odd_image_iff entry k hlevel hk hlower hnarrow
  · simp only [if_neg hnarrow]
    constructor
    · rintro ⟨a,hpar,ho⟩
      exact high_odd_bit_output_mod_nine a entry k
        hpar ho hlevel hlower
    · intro hdiv
      exact upper_high_odd_has_parent entry k hk hlevel (by omega) hdiv

#print axioms upper_high_odd_has_parent
#print axioms entire_high_odd_image_iff
end CascadeFastReturn
