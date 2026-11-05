import FatalRank
import ResetChain
set_option maxHeartbeats 0
namespace CascadeRank
open CascadeResetInverse CascadeSource CascadeManyShield

/-- Convert any genuine forward reset chain into an exact backward chain,
    retaining an explicit number of first-reset edges. -/
theorem reset_chain_has_reverse_path {start u : Nat}
    (hr : ResetChain start u) :
    ∃ steps, ReversePath u start steps := by
  induction hr with
  | root => exact ⟨0,ReversePath.stop _⟩
  | append hr hp ih =>
      obtain ⟨steps,hpath⟩ := ih
      exact ⟨steps+1,ReversePath.extend hp hpath⟩

/-- A valid inverse reset path back to its endpoint is exactly a source-level
    forward first-reset chain; this direction does not rely on any bounded
    search or experimental enumeration. -/
theorem reverse_path_implies_reset_chain {u start steps : Nat}
    (hp : ReversePath u start steps) : ResetChain start u := by
  induction hp with
  | stop u => exact ResetChain.root
  | extend hpar tail ih => exact ResetChain.append ih hpar

/-- The true post-initial blank-root fatal-height reachability criterion has
    an explicit quadratic maximum witness length in the fatal index. -/
theorem root_fatal_iff_bounded_reverse_path (n : Nat) (hn : 2≤n) :
    ReachC (2,0) (fatal n,0) ↔
      ∃ steps, steps≤(n+2)^2 ∧ ReversePath (fatal n) 2 steps := by
  constructor
  · intro hr
    obtain ⟨steps,hpath⟩ :=
      reset_chain_has_reverse_path ((root_reset_chain_iff (fatal n)).mp hr)
    exact ⟨steps,fatal_reverse_depth_le_quadratic n 2 steps hn hpath,hpath⟩
  · rintro ⟨steps,hbound,hpath⟩
    exact (root_reset_chain_iff (fatal n)).mpr
      (reverse_path_implies_reset_chain hpath)

#print axioms root_fatal_iff_bounded_reverse_path
end CascadeRank
