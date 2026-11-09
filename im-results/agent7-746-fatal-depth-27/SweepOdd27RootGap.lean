import SweepOddFatal27Upper
import UniqueEvenBand

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeUniformFatal CascadeSweep

/-- If a narrow high-band source target fails the exact 27-adic odd
    image criterion, every genuine first-reset parent must be the unique
    even predecessor at the same dyadic scale. -/
private theorem narrow_forced_even_parent (k e h q : Nat)
    (hk : 2≤k)
    (hlevel : firstFailIndex e=k)
    (hb : 6*2^k-1≤e ∧ e≤8*2^k-3)
    (hhigh : 6*2^k≤e)
    (hnarrow : 4*e+10<27*2^k)
    (hnodiv : (2*e+5)%27≠0)
    (heq : 2*e=8*2^k+h+k)
    (hp : ResetParent q e) :
    q=h := by
  have hnoOdd : ¬∃ a, (a+firstFailIndex a)%2=1 ∧
      bitOutcome a=some e := by
    intro hh
    exact hnodiv ((narrow_high_odd_image_iff e k hlevel hk hhigh hnarrow).mp hh)
  rcases hp with ⟨j,hbj,heqj⟩ | ⟨j,t,d,hd,hbj,hout,hq⟩
  · have hjk : j=k := even_band_scale_unique e j k hbj hb
    rw [hjk] at heqj
    omega
  · have hpar : (q+j)%2=1 := by omega
    have hlow : 4*2^j≤q+j+4 := by omega
    have hupper : q+j+5<8*2^j := by omega
    have hj : firstFailIndex q=j :=
      firstFailIndex_unique q j hupper
        (guards_from_low q j hlow)
    have hodd : (q+firstFailIndex q)%2=1 := by
      rw [hj]
      exact hpar
    have hreset : Outcome (q,0) (some e) :=
      reset_parent_sufficient q e (Or.inr ⟨j,t,d,hd,hbj,hout,hq⟩)
    have hbit : bitOutcome q=some e :=
      outcome_unique (bitOutcome_sound q) hreset
    exact False.elim (hnoOdd ⟨q,hodd,hbit⟩)

/-- A uniform source-verified blank-root exclusion for an entire
    high-entry narrow-band cylinder. The target e may itself have residue
    2 mod3 and thus admit an apparent odd inverse from a weaker mod3 test.
    Its odd parents are excluded by the new 27-adic image theorem;
    the unique even ancestor is then forced into a no-even-image gap. -/
theorem narrow_high_root_gap_exclusion (k e : Nat)
    (hk : 3≤k)
    (hlevel : firstFailIndex e=k)
    (hlower : 12*2^k+k+4≤2*e)
    (hnarrow : 4*e+10<27*2^k)
    (hdiv : (2*e+5)%27≠0)
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
    narrow_forced_even_parent k e h q (by omega) hlevel hb hhigh
      hnarrow hdiv heq hq
  rw [hqeq] at hqc
  exact hno ((root_reset_chain_iff h).mpr hqc)

/-- Non-vacuous example whose target is 2 mod3, so a simple mod3
    odd-parent exclusion does not prove its root unreachability. -/
theorem narrow_high_example_3083 :
    ¬ReachC (2,0) (3083,0) := by
  apply narrow_high_root_gap_exclusion 9 3083
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

#print axioms narrow_forced_even_parent
#print axioms narrow_high_root_gap_exclusion
#print axioms narrow_high_example_3083
end CascadeFastReturn
