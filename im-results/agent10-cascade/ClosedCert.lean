import Parents
import ResetChain

namespace CascadeResetInverse

/-- A candidate reverse cone is certified when every listed reset's entire
    complete source-C first-reset parent list lies within that cone. -/
def closedCert (s:List Nat) : Bool :=
  s.all (fun u => (parents u).all (fun h => s.contains h))

theorem closedCert_sound (s:List Nat) (hc:closedCert s=true) :
    ∀ u, u∈s → ∀h, ResetParent h u → h∈s := by
  intro u hu h hp
  have houter : (parents u).all (fun h => s.contains h)=true :=
    (List.all_eq_true.mp hc) u hu
  have hinner : s.contains h = true :=
    (List.all_eq_true.mp houter) h ((parents_iff h u).mpr hp)
  exact List.contains_iff_mem.mp hinner

/-- Finite closure and root exclusion imply unconditional nonreachability
    of the target from the genuine post-initial source-C root. This checker
    accepts only a complete exact first-reset inverse cone, never fuel
    exhaustion or a partial investigation. -/
theorem closedCert_excludes (s:List Nat) (u:Nat)
    (hc:closedCert s=true) (hm:u∈s) (hnot:2∉s) :
    ¬ CascadeSweep.ReachC (2,0) (u,0) := by
  intro hr
  have hr' := (root_reset_chain_iff u).mp hr
  have hclose := closedCert_sound s hc
  have hi : ∀x, ResetChain 2 x → x∈s → False := by
    intro x hx
    induction hx with
    | root => intro hm; exact hnot hm
    | append hx hp ih =>
        intro hm
        exact ih (hclose _ hm _ hp)
  exact hi u hr' hm

#print axioms closedCert_excludes
end CascadeResetInverse
