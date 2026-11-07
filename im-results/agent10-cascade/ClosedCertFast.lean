import ParentsFast
import ResetChain

/-!
A closed reverse-cone certificate checker using the kernel-reducible
parentsFast enumeration. This is equivalent to the source-C ResetChain
semantics, not a simulator-only reachability test.
-/

set_option maxHeartbeats 0
namespace CascadeResetInverse

/-- Every exact ResetParent predecessor of each listed height is listed. -/
def closedCertFast (S : List Nat) : Bool :=
  S.all (fun u => (parentsFast u).all (fun h => S.contains h))

theorem closedCertFast_sound (S : List Nat) (hc : closedCertFast S = true)
    {u h : Nat} (hu : u ∈ S) (hp : ResetParent h u) : h ∈ S := by
  have houter : (parentsFast u).all (fun h => S.contains h) = true :=
    (List.all_eq_true.mp hc) u hu
  have hinner : S.contains h = true :=
    (List.all_eq_true.mp houter) h ((parentsFast_iff h u).mpr hp)
  exact List.contains_iff_mem.mp hinner

/-- A closed cone excluding 2 proves the target is not on the blank-root
    source-C trajectory, via the exact reset-chain equivalence. -/
theorem closedCertFast_excludes (u : Nat) (S : List Nat)
    (hc : closedCertFast S = true) (hu : u ∈ S) (h2 : 2 ∉ S) :
    ¬ ReachC (2,0) (u,0) := by
  intro hr
  have hchain : ResetChain 2 u := (root_reset_chain_iff u).mp hr
  have hclose : ∀ x, ResetChain 2 x → x ∈ S → False := by
    intro x hx
    induction hx with
    | root => intro hm; exact h2 hm
    | append hx hp ih =>
        intro hm
        exact ih (closedCertFast_sound S hc hm hp)
  exact hclose u hchain hu

#print axioms closedCertFast_sound
#print axioms closedCertFast_excludes
end CascadeResetInverse
