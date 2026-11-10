import ForkFamily
import FirstFork
set_option maxHeartbeats 0

namespace BB746Fork

/-- All-time authentic-blank-root exclusion of a genuine valuation-one
odd first-reset predecessor for four infinite families of fatal levels.
This does not exclude the fatal height's other predecessor branches. -/
theorem fatal_odd_feeder_four_classes (r t : Nat)
    (hr : r=40 ∨ r=401 ∨ r=1012 ∨ r=1373) :
    let n := r+1458*t
    CascadeResetInverse.ResetParent
      (CascadeFirstFork.oddPre n (CascadeManyShield.fatal n))
      (CascadeManyShield.fatal n) ∧
    ¬CascadeSweep.ReachC (2,0)
      (CascadeFirstFork.oddPre n (CascadeManyShield.fatal n),0) := by
  let n := r+1458*t
  let k := n-2
  let p := 2^k
  let u := 4*2^n-n-4
  let d := (2*u+5)/9
  let x := 4*d-8*p-n-3
  have hn : 40≤n := by
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp [n] <;> omega
  have hk : k+2=n := by dsimp [k]; omega
  have hres : n%18=4 ∨ n%18=5 := by
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp [n] <;> omega
  have hparent : CascadeResetInverse.ResetParent
      (CascadeFirstFork.oddPre n (CascadeManyShield.fatal n))
      (CascadeManyShield.fatal n) :=
    CascadeFirstFork.fatal_has_odd_parent n (by omega) hres
  have heq : CascadeFirstFork.oddPre n (CascadeManyShield.fatal n)=x := by
    change 4*((2*u+5)/9)-8*p-k-5=x
    dsimp [x,d]
    omega
  have hno : ¬ResetChain 2 x := infinite_fatal_feeder_gap r t hr
  exact ⟨hparent,by
    rw [heq]
    intro hreach
    exact hno ((CascadeResetInverse.root_reset_chain_iff x).mp hreach)⟩

#print axioms fatal_odd_feeder_four_classes
end BB746Fork
