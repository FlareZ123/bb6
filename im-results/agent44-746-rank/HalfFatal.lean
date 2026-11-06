import HalfDepth
import RootDepth
set_option maxHeartbeats 0
namespace CascadeHalfRank
open CascadeRank CascadeSweep CascadeManyShield

/-- Every genuine source inverse ancestry of a candidate #746 fatal reset
    has a triangular bound in its fatal index. -/
theorem fatal_inverse_depth_le_triangle (n v steps : Nat)
    (hn : 2≤n) (hp : ReversePath (fatal n) v steps) :
    steps ≤ tri (n+2) := by
  have hb := reverse_path_length_le_triangle (fatal n) v steps hp
  rw [CascadeFastShield.fatal_log2 n hn] at hb
  have hs : n+1+1=n+2 := by omega
  simpa only [hs] using hb

/-- The true post-initial source-root fatal-height reachability criterion
    has a triangular maximum witness length for every candidate index. -/
theorem root_fatal_iff_triangular_reverse_path (n : Nat) (hn : 2≤n) :
    ReachC (2,0) (fatal n,0) ↔
      ∃steps, steps≤tri (n+2) ∧ ReversePath (fatal n) 2 steps := by
  constructor
  · intro hr
    obtain ⟨steps, _, hp⟩ :=
      (CascadeRank.root_fatal_iff_bounded_reverse_path n hn).mp hr
    exact ⟨steps,fatal_inverse_depth_le_triangle n 2 steps hn hp,hp⟩
  · rintro ⟨steps, _, hp⟩
    exact (CascadeRank.root_fatal_iff_bounded_reverse_path n hn).mpr
      ⟨steps,CascadeRank.fatal_reverse_depth_le_quadratic n 2 steps hn hp,hp⟩

/-- Closed, division-free version of the fatal-index depth bound. -/
theorem fatal_inverse_depth_le_half_quadratic (n v steps : Nat)
    (hn : 2≤n) (hp : ReversePath (fatal n) v steps) :
    2*steps ≤ (n+2)*(n+3) := by
  have hb := reverse_path_length_le_half_quadratic (fatal n) v steps hp
  rw [CascadeFastShield.fatal_log2 n hn] at hb
  have hs : n+1+1=n+2 := by omega
  have ht : n+1+2=n+3 := by omega
  simpa only [hs,ht] using hb

#print axioms fatal_inverse_depth_le_half_quadratic
#print axioms root_fatal_iff_triangular_reverse_path
end CascadeHalfRank
