import FirstInverseComplete
import SweepInvariant

namespace CascadeResetInverse
open CascadeSource CascadeSweep

/-- A source-C trajectory segment from a reset h, with every subsequent
    state still in-flight (its right counter is nonzero). -/
inductive Pending (h : Nat) : (Nat × Nat) → Prop where
  | root : Pending h (h,0)
  | follow {x y : Nat × Nat} (hp : Pending h x)
      (he : Cstep x.1 x.2=some y) (hy : y.2≠0) : Pending h y

private theorem pending_lift {h : Nat} {x : Nat × Nat} {o : Option Nat}
    (hp : Pending h x) (ho : Outcome x o) : Outcome (h,0) o := by
  induction hp generalizing o with
  | root => exact ho
  | follow hp he hy ih => exact ih (Outcome.follow he hy ho)

/-- Genuine first-reset edge closure at reset-level granularity. -/
inductive ResetChain (start : Nat) : Nat → Prop where
  | root : ResetChain start start
  | append {h u : Nat} (hr : ResetChain start h)
      (hp : ResetParent h u) : ResetChain start u

/-- Every compressed C-path from blank-root C(2,0) has a unique most recent
    reset, whose full first-reset ancestors form a ResetParent chain. -/
theorem cpath_has_reset_chain {x : Nat × Nat}
    (hr : ReachC (2,0) x) :
    ∃ h, ResetChain 2 h ∧ Pending h x := by
  induction hr with
  | refl =>
    exact ⟨2,ResetChain.root,Pending.root⟩
  | push hr he ih =>
    rename_i y z
    obtain ⟨h,hc,hp⟩ := ih
    rcases z with ⟨u,v⟩
    by_cases hv : v=0
    · subst v
      have hfirst : Outcome (h,0) (some u) :=
        pending_lift hp (Outcome.reset he)
      have hparent : ResetParent h u := (reset_parent_iff h u).mp hfirst
      exact ⟨u,ResetChain.append hc hparent,Pending.root⟩
    · exact ⟨h,hc,Pending.follow hp he (by simpa using hv)⟩

private theorem reach_trans {x y z : Nat × Nat}
    (hxy : ReachC x y) (hyz : ReachC y z) : ReachC x z := by
  induction hyz with
  | refl => exact hxy
  | push hp he ih => exact ReachC.push ih he

private theorem outcome_to_reach_aux {x : Nat × Nat} {o : Option Nat}
    (ho : Outcome x o) : ∀u, o=some u → ReachC x (u,0) := by
  induction ho with
  | halt he =>
      intro u heq
      cases heq
  | reset he =>
      intro u heq
      cases heq
      exact ReachC.push (ReachC.refl _) he
  | follow he hy hr ih =>
      intro u heq
      exact reach_trans (ReachC.push (ReachC.refl _) he) (ih u heq)

private theorem outcome_to_reach {x : Nat × Nat} {u : Nat}
    (ho : Outcome x (some u)) : ReachC x (u,0) :=
  outcome_to_reach_aux ho u rfl

/-- Every algebraic first-reset chain corresponds to genuine source-C
    reachability; the converse is cpath_has_reset_chain. -/
theorem reset_chain_to_cpath {s u : Nat}
    (hr : ResetChain s u) : ReachC (s,0) (u,0) := by
  induction hr with
  | root => exact ReachC.refl _
  | append hr hp ih =>
      have hfirst := (reset_parent_iff _ _).mpr hp
      exact reach_trans ih (outcome_to_reach hfirst)

/-- **Exact reset-level semantics** of the post-initial #746 source-C
    trajectory. The full C-state reachability problem for reset targets is
    equivalent to the finite-chain closure of ResetParent. No approximation
    or missed intermediate sweep states remain. -/
theorem root_reset_chain_iff (u : Nat) :
    ReachC (2,0) (u,0) ↔ ResetChain 2 u := by
  constructor
  · intro hr
    obtain ⟨h,hchain,hpending⟩ := cpath_has_reset_chain hr
    cases hpending with
    | root => exact hchain
    | follow hp he hy => simp at hy
  · exact reset_chain_to_cpath

#print axioms root_reset_chain_iff
#print axioms cpath_has_reset_chain
#print axioms reset_chain_to_cpath
end CascadeResetInverse
