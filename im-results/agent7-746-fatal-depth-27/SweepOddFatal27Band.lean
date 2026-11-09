import SweepOddFatal27Source

namespace CascadeFastReturn
open CascadeBitSweep

/-- The narrow high-level image interval has an exact converse:
    divisibility by 27 constructs a source-valid odd first-reset predecessor
    with valuation exponent t=2 and sweep index j=k-2. -/
theorem narrow_high_odd_has_parent (entry k : Nat)
    (hk : 2≤k)
    (hhigh : 6*2^k≤entry)
    (htop : 4*entry+10<27*2^k)
    (hdiv : (2*entry+5)%27=0) :
    ∃a, (a+firstFailIndex a)%2=1 ∧ bitOutcome a=some entry := by
  let j := k-2
  let d := (2*entry+5)/27
  let q := 2^2*d
  let a := 2*q-8*2^j-j-5
  have hj : j+2=k := by dsimp [j]; omega
  have hpow : 2^k=4*2^j := by
    rw [←hj,show j+2=(j+1)+1 by omega, Nat.pow_succ, Nat.pow_succ]
    omega
  have hdn : 27*d=2*entry+5 := by dsimp [d]; omega
  have hodd : d%2=1 := by omega
  have hq : q=4*d := by simp [q]
  have hb1 : 6*2^j+1≤q := by rw [hq]; omega
  have hb2 : q≤8*2^j-1 := by rw [hq]; omega
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
  have heqout : 2*entry+5=3^(2+1)*d := by
    have hn : 3^(2+1)=27 := by decide
    rw [hn]
    omega
  have hparent : CascadeResetInverse.ResetParent a entry :=
    Or.inr ⟨j,2,d,hodd,⟨hb1,hb2⟩,heqout,heq⟩
  have hr := CascadeResetInverse.reset_parent_sufficient a entry hparent
  have hb := bitOutcome_sound a
  exact ⟨a,hpar,CascadeResetInverse.outcome_unique hb hr⟩

/-- Exact characterization of the narrow high-level image of odd source
    first resets. This concerns all natural synthetic heights; no blank
    reachability assumption is made. -/
theorem narrow_high_odd_image_iff (entry k : Nat)
    (hk : firstFailIndex entry=k)
    (hk2 : 2≤k)
    (hhigh : 6*2^k≤entry)
    (htop : 4*entry+10<27*2^k) :
    (∃a, (a+firstFailIndex a)%2=1 ∧ bitOutcome a=some entry) ↔
      (2*entry+5)%27=0 := by
  constructor
  · rintro ⟨a,hpar,ho⟩
    exact narrow_high_odd_output_mod_twentyseven a entry k
      hpar ho hk hhigh htop
  · intro hdiv
    exact narrow_high_odd_has_parent entry k hk2 hhigh htop hdiv

#print axioms narrow_high_odd_has_parent
#print axioms narrow_high_odd_image_iff
end CascadeFastReturn
