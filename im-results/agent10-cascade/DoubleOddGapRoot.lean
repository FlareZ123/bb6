import MiddleLowOddExact

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeUniformFatal CascadeSweep

/-- If a narrow-high target fails the exact mod-27 odd-image test,
    every actual first-reset parent is the unique even parent at k. -/
private theorem narrow_27_forced_even (k e h q : Nat)
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
    exact hnodiv
      ((narrow_high_odd_image_iff e k hlevel hk hhigh hnarrow).mp hh)
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

/-- Two consecutive modular obstructions genuinely exclude blank-root
    reachability even where both the target e and its only possible
    predecessor h can be 2 modulo 3. First, 27-divisibility fails
    in the narrow high band of e; then 9-divisibility fails for
    h = 2e - 8·2^k - k in the middle-low no-even-image band. -/
theorem narrow_27_middle9_root_exclusion (k e : Nat)
    (hk : 3≤k)
    (hlevel : firstFailIndex e=k)
    (hlower : 12*2^k+k+4≤2*e)
    (hnarrow : 4*e+10<27*2^k)
    (hdiv27 : (2*e+5)%27≠0)
    (hmiddle : 2*(2*e-8*2^k-k)+5<9*2^k)
    (hdiv9 : (2*(2*e-8*2^k-k)+5)%9≠0) :
    ¬ReachC (2,0) (e,0) := by
  let h := 2*e-8*2^k-k
  have hlarge : 8*2^k+k≤2*e := by omega
  have hlow : 4*2^k≤h := by dsimp [h]; omega
  have heq : 2*e=8*2^k+h+k := by dsimp [h]; omega
  have hno : ¬ReachC (2,0) (h,0) :=
    middle_low_root_nonimage k h hk hlow
      (by simpa only [h] using hmiddle)
      (by simpa only [h] using hdiv9)
  have hguard := (firstFailIndex_spec e).2
  rw [hlevel] at hguard
  have hb : 6*2^k-1≤e ∧ e≤8*2^k-3 := by omega
  have hhigh : 6*2^k≤e := by omega
  have he_ne : e≠2 := by omega
  intro hr
  have hc : ResetChain 2 e := (root_reset_chain_iff e).mp hr
  obtain ⟨q,hqc,hq⟩ := reset_chain_last hc he_ne
  have hqeq : q=h :=
    narrow_27_forced_even k e h q (by omega) hlevel hb hhigh
      hnarrow hdiv27 heq hq
  rw [hqeq] at hqc
  exact hno ((root_reset_chain_iff h).mpr hqc)

/-- Explicit first example of a doubly 2-mod-3 target and forced
    predecessor eliminated only after independent 27- and 9-adic sieves.
    At k=12, e=24593 and h=16406. -/
theorem narrow_double_example :
    ¬ReachC (2,0) (24593,0) := by
  apply narrow_27_middle9_root_exclusion 12 24593
  all_goals decide

#print axioms narrow_27_middle9_root_exclusion
#print axioms narrow_double_example
end CascadeFastReturn
