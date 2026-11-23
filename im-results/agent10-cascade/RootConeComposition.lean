import TerminalFirstForkLeaf
import TerminalHighBandLeaf

set_option maxHeartbeats 0

namespace CascadeRootConeComposition
open CascadeResetInverse CascadeSweep
open CascadeTerminalFirstFork CascadeTerminalHighBand

/-- Source-connected closure principle: an ordinary reset target is
    unreachable from the real blank C(2,0) root when all its exact
    first-reset predecessors are unreachable. Every valuation of the
    source ResetParent relation is retained; no finite-depth cutoff. -/
theorem root_excluded_of_all_parents_dead (u : Nat)
    (hu : u ≠ 2)
    (hd : ∀ h, ResetParent h u → ¬ ReachC (2,0) (h,0)) :
    ¬ ReachC (2,0) (u,0) := by
  intro hr
  have hc : ResetChain 2 u := (root_reset_chain_iff u).mp hr
  cases hc with
  | root => exact hu rfl
  | append hpchain hp =>
    have hreach : ReachC (2,0) (_,0) :=
      (root_reset_chain_iff _).mpr hpchain
    exact (hd _ hp) hreach

/-- Exact two-way source reset-fork closure, allowing arbitrary
    extra valuation witnesses only if they have already been ruled
    out in the universal parent-coverage hypotheses. -/
theorem rooted_two_fork_closed (v w z h : Nat)
    (hv : v ≠ 2) (hw : w ≠ 2)
    (hz : ¬ ReachC (2,0) (z,0))
    (hh : ¬ ReachC (2,0) (h,0))
    (hparents : ∀ q, ResetParent q v → q = w ∨ q = h)
    (hwparents : ∀ q, ResetParent q w → q = z) :
    ¬ ReachC (2,0) (v,0) := by
  have hwd : ¬ ReachC (2,0) (w,0) :=
    root_excluded_of_all_parents_dead w hw (by
      intro x hx
      have heq : x = z := hwparents x hx
      subst x
      exact hz)
  exact root_excluded_of_all_parents_dead v hv (by
    intro x hx
    rcases hparents x hx with rfl | rfl
    · exact hwd
    · exact hh)

/-- The compositional conclusion used to close the authentic J-2
    canonical-ray fork: the abstract terminal high-c leaf and the
    arithmetic t=1 feeder leaf close *both* legal first-reset arms
    once complete universal parent classification is provided. -/
theorem ray_nonterminal_fork_closed
    (n p q Q u v w z h d s : Nat)
    (hn : 257 ≤ n)
    (hp : p = 2^n)
    (hpbig : n+16 < p)
    (hhigh : 7*p < 4*q)
    (hqbound : q < 2*p)
    (hqfour : q=4*Q)
    (hvlin : v+Q+1=4*p+n)
    (hXd : 2*v+5=9*d)
    (hdmod : d%3=1)
    (hhlin : h+2*p+n+3=4*d)
    (hsector : (2*p+n)%3=0)
    (hzlin : z+q+1=4*p+n)
    (hhighstrong : 7*p+4*s ≤ 4*q)
    (hs : n+5 ≤ s)
    (hzmod : (2*z+5)%9≠0)
    (hvne : v≠2) (hwne : w≠2)
    (hparents : ∀ r, ResetParent r v → r=w ∨ r=h)
    (hwparents : ∀ r, ResetParent r w → r=z) :
    ¬ ReachC (2,0) (v,0) := by
  have hlinear : 9*h+2*q+n+15=14*p := by omega
  have hhroot : ¬ReachC (2,0) (h,0) :=
    tone_feeder_nonterminal_gap_dead n p q d h
       hn hp hpbig hhigh hqbound hlinear
       hsector hdmod hhlin
  have hzroot : ¬ReachC (2,0) (z,0) :=
    terminal_high_root_excluded n p q s z
      hn hp hzlin hqbound hhighstrong hs hzmod
  exact rooted_two_fork_closed v w z h hvne hwne hzroot hhroot
    hparents hwparents

#print axioms root_excluded_of_all_parents_dead
#print axioms rooted_two_fork_closed
#print axioms ray_nonterminal_fork_closed
end CascadeRootConeComposition
