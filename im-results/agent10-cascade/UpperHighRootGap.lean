import SweepOdd27RootGap

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeUniformFatal CascadeSweep

/-- In the upper high target band, failure of the exact mod-nine odd-image
    condition forces every original first-reset parent to be the one even
    predecessor at the target's dyadic scale. -/
private theorem upper_forced_even_parent (k e h q : Nat)
    (hk : 2≤k)
    (hlevel : firstFailIndex e=k)
    (hb : 6*2^k-1≤e ∧ e≤8*2^k-3)
    (hhigh : 6*2^k≤e)
    (hupper : 27*2^k≤4*e+10)
    (hnodiv : (2*e+5)%9≠0)
    (heq : 2*e=8*2^k+h+k)
    (hp : ResetParent q e) :
    q=h := by
  have hnoOdd : ¬∃ a, (a+firstFailIndex a)%2=1 ∧
      bitOutcome a=some e := by
    intro hh
    have hc := (entire_high_odd_image_iff e k hlevel hk hhigh).mp hh
    have hnarrow : ¬4*e+10<27*2^k := by omega
    simp only [if_neg hnarrow] at hc
    exact hnodiv hc
  rcases hp with ⟨j,hbj,heqj⟩ | ⟨j,t,d,hd,hbj,hout,hq⟩
  · have hjk : j=k := even_band_scale_unique e j k hbj hb
    rw [hjk] at heqj
    omega
  · have hpar : (q+j)%2=1 := by omega
    have hlow : 4*2^j≤q+j+4 := by omega
    have hmax : q+j+5<8*2^j := by omega
    have hj : firstFailIndex q=j :=
      firstFailIndex_unique q j hmax (guards_from_low q j hlow)
    have hodd : (q+firstFailIndex q)%2=1 := by
      rw [hj]
      exact hpar
    have hr : Outcome (q,0) (some e) :=
      reset_parent_sufficient q e (Or.inr ⟨j,t,d,hd,hbj,hout,hq⟩)
    have hbit : bitOutcome q=some e :=
      outcome_unique (bitOutcome_sound q) hr
    exact False.elim (hnoOdd ⟨q,hodd,hbit⟩)

/-- Genuine blank-start exclusion in the *upper* high image band
    27*2^k ≤ 4e+10. The image theorem forces an even parent, whose
    height lies in the universal dyadic non-even-image gap; residue
    modulo three then excludes its odd parents as well. Unlike the
    earlier narrow-band theorem, this covers e ≥ 27*2^(k-2). -/
theorem upper_high_root_gap_exclusion (k e : Nat)
    (hk : 3≤k)
    (hlevel : firstFailIndex e=k)
    (hlower : 12*2^k+k+4≤2*e)
    (hceiling : 2*e+2≤14*2^k+k)
    (hupper : 27*2^k≤4*e+10)
    (hdiv : (2*e+5)%9≠0)
    (hparentmod : (2*e-8*2^k-k)%3≠2) :
    ¬ReachC (2,0) (e,0) := by
  let h := 2*e-8*2^k-k
  have hmin : 4*2^k-3<h := by dsimp [h]; omega
  have hmax : h<6*2^k-1 := by dsimp [h]; omega
  have hlarge : 8*2^k+k≤2*e := by omega
  have heq : 2*e=8*2^k+h+k := by dsimp [h]; omega
  have hguard := (firstFailIndex_spec e).2
  rw [hlevel] at hguard
  have hb : 6*2^k-1≤e ∧ e≤8*2^k-3 := by omega
  have hhigh : 6*2^k≤e := by omega
  have he_ne : e≠2 := by omega
  have hgap : ∀ j, ¬(6*2^j-1≤h ∧ h≤8*2^j-3) := by
    intro j
    have hshift : (k+1)-1=k := by omega
    exact TerminalExit.no_even_band (k+1) j h
      (by omega) (by simpa [hshift] using hmin)
      (by simpa [hshift] using hmax)
  have hno : ¬ReachC (2,0) (h,0) :=
    root_excludes_nonimage h (by simpa [h] using hparentmod) hgap
  intro hr
  have hc : ResetChain 2 e := (root_reset_chain_iff e).mp hr
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc he_ne
  have hqeq : q=h :=
    upper_forced_even_parent k e h q (by omega) hlevel hb hhigh
      hupper hdiv heq hq
  rw [hqeq] at hqc
  exact hno ((root_reset_chain_iff h).mpr hqc)

/-- First explicit upper-band source root exclusion. Target 6917 has
    residue two modulo three, yet the stronger odd-image test rules
    out every odd reset ancestor. -/
theorem upper_high_example_6917 :
    ¬ReachC (2,0) (6917,0) := by
  apply upper_high_root_gap_exclusion 10 6917
  all_goals decide

#print axioms upper_forced_even_parent
#print axioms upper_high_root_gap_exclusion
#print axioms upper_high_example_6917
end CascadeFastReturn
