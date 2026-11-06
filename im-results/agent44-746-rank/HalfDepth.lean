import HalfResetRank
import ResetRank
set_option maxHeartbeats 0
namespace CascadeHalfRank
open CascadeRank

/-- A sharp triangular bound obtained from the strict triangular rank. -/
theorem reverse_path_length_le_half_rank (u v steps : Nat)
    (hp : ReversePath u v steps) : steps ≤ halfRank u := by
  induction hp with
  | stop u => omega
  | @extend u h v steps par tail ih =>
      have he := reset_parent_half_rank_decreases h u par
      omega

/-- Every genuine inverse path has length at most the triangular number
    T_(floor(log2(u))+1), halving the leading quadratic coefficient. -/
theorem reverse_path_length_le_triangle (u v steps : Nat)
    (hp : ReversePath u v steps) : steps ≤ tri (u.log2+1) := by
  have hh := reverse_path_length_le_half_rank u v steps hp
  dsimp [halfRank] at hh
  omega

/-- Division-free closed version of the triangular inverse-depth bound. -/
theorem reverse_path_length_le_half_quadratic (u v steps : Nat)
    (hp : ReversePath u v steps) :
    2*steps ≤ (u.log2+1)*(u.log2+2) := by
  have hh := reverse_path_length_le_triangle u v steps hp
  have ht : 2*tri (u.log2+1)=(u.log2+1)*(u.log2+2) := by
    simpa [Nat.add_assoc] using tri_closed (u.log2+1)
  omega

#print axioms reverse_path_length_le_half_quadratic
end CascadeHalfRank
