import ResetRank
import FastShield
set_option maxHeartbeats 0
namespace CascadeRank
open CascadeSource

/-- The #746 candidate fatal reset heights have uniformly quadratic maximal
    inverse path length in their fatal-index parameter n. -/
theorem fatal_reverse_depth_le_quadratic (n v depth : Nat)
    (hn : 2≤n)
    (hp : ReversePath (fatal n) v depth) :
    depth ≤ (n+2)^2 := by
  have hb := reverse_path_length_le_log_square (fatal n) v depth hp
  rw [CascadeFastShield.fatal_log2 n hn] at hb
  have hs : n+1+1=n+2 := by omega
  simpa only [hs] using hb

#print axioms fatal_reverse_depth_le_quadratic
end CascadeRank
