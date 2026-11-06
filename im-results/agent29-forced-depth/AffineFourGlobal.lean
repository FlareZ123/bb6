import BottomBoundary
import AffineNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Bottom

/-- Exact original-source affine inversion preserves odd left coordinates
    at least five. This holds for arbitrarily many recursive inverse links. -/
theorem affine_normalize_odd_ge_five (a k : Nat)
    (ha : a%2=1) (hbig : 5≤a) :
    (BB6.Agent15.affineNormalize a k).1%2=1 ∧
      5≤(BB6.Agent15.affineNormalize a k).1 := by
  induction k using Nat.strongRecOn generalizing a with
  | ind k ih =>
      by_cases h : 4≤k ∧ k%2=0 ∧ (a+k)%4=1
      · have hk : (k-2)/2<k := by omega
        have hah : (a+k-2)%2=1 := by omega
        have hlarge : 5≤a+k-2 := by omega
        rw [BB6.Agent15.affineNormalize,dif_pos h]
        exact ih _ hk (a+k-2) hah hlarge
      · rw [BB6.Agent15.affineNormalize,dif_neg h]
        exact ⟨ha,hbig⟩

/-- True-blank exclusion for every odd-left input a≥5 whose genuine
    unbounded affine normalizer has residual right counter four.
    No halting equation, depth bound or parametrization is assumed. -/
theorem blank_no_affine_four_odd_ge_five (a k : Nat)
    (ha : a%2=1) (hbig : 5≤a)
    (hfour : (BB6.Agent15.affineNormalize a k).2=4) :
    ¬ BB6.Agent15.CReach a k := by
  intro hr
  have hn := affine_normalize_odd_ge_five a k ha hbig
  obtain ⟨time,ht⟩ :=
    (BB6.Agent15.reach_iff_normalize a k).mp hr
  have htarget :
      BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) =
        some ((BB6.Agent15.affineNormalize a k).1,4) := by
    simpa only [hfour] using ht
  exact blank_odd_four_gt_three_unreachable time
    (BB6.Agent15.affineNormalize a k).1 hn.1 (by omega) htarget

/-- Complete true-blank reachability classification inside the entire
    odd-left >=3, affine-residual-right-four sector. The unique reachable
    member is precisely the authentic first return (3,4). -/
theorem blank_affine_four_odd_ge_three_iff (a k : Nat)
    (ha : a%2=1) (hbig : 3≤a)
    (hfour : (BB6.Agent15.affineNormalize a k).2=4) :
    BB6.Agent15.CReach a k ↔ a=3 ∧ k=4 := by
  constructor
  · intro hr
    by_cases hfive : 5≤a
    · exact False.elim
        ((blank_no_affine_four_odd_ge_five a k ha hfive hfour) hr)
    · have ha3 : a=3 := by omega
      subst a
      by_cases hgate : 4≤k ∧ k%2=0 ∧ ((3:Nat)+k)%4=1
      · have hparity : (3+k-2)%2=1 := by omega
        have hlarge : 5≤3+k-2 := by omega
        have hn : (BB6.Agent15.affineNormalize
            (3+k-2) ((k-2)/2)).2=4 := by
          rw [BB6.Agent15.affineNormalize, dif_pos hgate] at hfour
          exact hfour
        have hparent : BB6.Agent15.CReach (3+k-2) ((k-2)/2) :=
          (BB6.Agent15.blank_reach_iff_affine 3 k
            hgate.1 hgate.2.1 hgate.2.2).mp hr
        exact False.elim
          ((blank_no_affine_four_odd_ge_five (3+k-2)
              ((k-2)/2) hparity hlarge hn) hparent)
      · have hright : k=4 := by
          rw [BB6.Agent15.affineNormalize, dif_neg hgate] at hfour
          exact hfour
        exact ⟨rfl,hright⟩
  · rintro ⟨haeq,hkeq⟩
    subst a
    subst k
    have hstep : BB6.Agent46.secNext (5,1)=some (3,4) := by decide
    exact ⟨1,by simpa [BB6.Agent8Section.run] using hstep⟩

/-- The one-left sector can never itself have normalized right
    counter four: an eligible affine first step leaves an odd right
    coordinate, and an ineligible step leaves the original right. -/
theorem affine_normalize_one_ne_four (k : Nat) :
    (BB6.Agent15.affineNormalize 1 k).2≠4 := by
  by_cases h : 4≤k ∧ k%2=0 ∧ ((1:Nat)+k)%4=1
  · have hk4 : k%4=0 := by omega
    have hnext : ¬ (4≤(k-2)/2 ∧ ((k-2)/2)%2=0 ∧
      ((1+k-2)+(k-2)/2)%4=1) := by omega
    rw [BB6.Agent15.affineNormalize, dif_pos h]
    rw [BB6.Agent15.affineNormalize, dif_neg hnext]
    omega
  · have hn : BB6.Agent15.affineNormalize 1 k=(1,k) := by
      rw [BB6.Agent15.affineNormalize,dif_neg h]
    rw [hn]
    intro heq
    have hk : k=4 := by simpa using heq
    subst k
    exact h (by decide)

/-- COMPLETE original-blank classification of the entire odd-first affine
    terminal right-four sector, without an initial first-counter lower
    bound, an inverse-depth bound, or any stopping equation. -/
theorem blank_affine_four_odd_iff (a k : Nat)
    (ha : a%2=1)
    (hfour : (BB6.Agent15.affineNormalize a k).2=4) :
    BB6.Agent15.CReach a k ↔ a=3 ∧ k=4 := by
  have hcases : a=1 ∨ 3≤a := by omega
  rcases hcases with h1 | h3
  · subst a
    exact False.elim ((affine_normalize_one_ne_four k) hfour)
  · exact blank_affine_four_odd_ge_three_iff a k ha h3 hfour

#print axioms affine_normalize_one_ne_four
#print axioms blank_affine_four_odd_iff
#print axioms blank_affine_four_odd_ge_three_iff
#print axioms affine_normalize_odd_ge_five
#print axioms blank_no_affine_four_odd_ge_five
end BB6.Agent29Bottom
