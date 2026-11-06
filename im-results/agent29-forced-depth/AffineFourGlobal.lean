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

#print axioms affine_normalize_odd_ge_five
#print axioms blank_no_affine_four_odd_ge_five
end BB6.Agent29Bottom
