import Agent49ParitySource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
# Exact source counterexample to a state-local 3-adic min-counter bound

The candidate bound v3(min(a,d)) <= k-2 is observed on a finite blank-root
prefix, where k is the least exponent with 3^k > 34*ell_S+122.  This file
certifies a source-authentic transition in the affine cone where the bound
holds at the source and fails at the target.  Thus it cannot be a state-local
forward invariant.
-/

namespace BB6.Agent41V3MinCounterexample

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

/-- Exact successful transition under the unmodified upstream highLevelNext. -/
theorem v3_candidate_counterexample_step :
    highLevelNext (.D 464905666 116226414) =
      some (.D 348679242 348679292) := by
  decide +kernel

/-- The source mass has depth ell_S=20. -/
theorem source_mass_depth_20 :
    3^19 < 2*(464905666+116226414)+7 ∧
    2*(464905666+116226414)+7 ≤ 3^20 := by
  norm_num

/-- The target mass also has depth ell_S=20. -/
theorem target_mass_depth_20 :
    3^19 < 2*(348679242+348679292)+7 ∧
    2*(348679242+348679292)+7 ≤ 3^20 := by
  norm_num

/-- At ell=20, B=34*ell+122=802 and k=7. -/
theorem buffer_exponent_20 :
    34*20+122=802 ∧ 3^6 ≤ 802 ∧ 802 < 3^7 := by
  norm_num

/-- Stronger source-authentic transition: even the weaker v3(min)<=k
    predicate is not forward-closed on the affine cone. -/
theorem v3_at_k_counterexample_step :
    highLevelNext (.D 465026190 116256546) =
      some (.D 348769638 348769680) := by
  decide +kernel

/-- The stronger counterexample's source and target both have ell_S=20. -/
theorem v3_at_k_source_mass_depth_20 :
    3^19 < 2*(465026190+116256546)+7 ∧
    2*(465026190+116256546)+7 ≤ 3^20 := by
  norm_num

theorem v3_at_k_target_mass_depth_20 :
    3^19 < 2*(348769638+348769680)+7 ∧
    2*(348769638+348769680)+7 ≤ 3^20 := by
  norm_num

/-- The stronger counterexample's source smaller counter has exact v3=7. -/
theorem v3_at_k_source_min_v3_seven :
    3^7 ∣ 116256546 ∧ ¬ 3^8 ∣ 116256546 := by
  norm_num

/-- The stronger counterexample's target smaller counter has exact v3=8. -/
theorem v3_at_k_target_min_v3_eight :
    3^8 ∣ 348769638 ∧ ¬ 3^9 ∣ 348769638 := by
  norm_num

/-- The weaker candidate v3(min)<=k holds at the source (7<=7). -/
theorem v3_at_k_source_satisfies_candidate :
    7 ≤ 7 := by omega

/-- The weaker candidate v3(min)<=k fails at the target (8>7). -/
theorem v3_at_k_target_violates_candidate :
    ¬ 8 ≤ 7 := by omega

/-- The source smaller counter has exact 3-adic valuation 5. -/
theorem source_min_v3_five :
    3^5 ∣ 116226414 ∧ ¬ 3^6 ∣ 116226414 := by
  norm_num

/-- The target smaller counter has exact 3-adic valuation 6. -/
theorem target_min_v3_six :
    3^6 ∣ 348679242 ∧ ¬ 3^7 ∣ 348679242 := by
  norm_num

/-- The candidate v3(min)<=k-2 holds at the source (5<=5). -/
theorem source_satisfies_candidate :
    5 ≤ 7-2 := by omega

/-- The candidate v3(min)<=k-2 fails at the target (6>5). -/
theorem target_violates_candidate :
    ¬ 6 ≤ 7-2 := by omega

#print axioms v3_candidate_counterexample_step
#print axioms v3_at_k_counterexample_step
#print axioms v3_at_k_source_mass_depth_20
#print axioms v3_at_k_target_mass_depth_20
#print axioms v3_at_k_source_min_v3_seven
#print axioms v3_at_k_target_min_v3_eight
#print axioms source_mass_depth_20
#print axioms target_mass_depth_20
#print axioms buffer_exponent_20
#print axioms source_min_v3_five
#print axioms target_min_v3_six

end BB6.Agent41V3MinCounterexample
