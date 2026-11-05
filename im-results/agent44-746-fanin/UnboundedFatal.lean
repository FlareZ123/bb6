import ManyParents
import FatalValuationBeyond
set_option maxHeartbeats 0
namespace CascadeAgent44
open CascadeManyShield CascadeFatalValuation CascadeResetInverse

/-- In each surviving #746 fatal-index sector, arbitrarily large indices
    have arbitrarily many *distinct genuine first-reset* odd predecessors.
    The real blank-root reachability of these targets remains open. -/
theorem fatal_unbounded_odd_fanin_four (N M : Nat) :
    ∃ n, N<n ∧ n%6=4 ∧
      ∃ f : Fin M → Nat, Function.Injective f ∧
        ∀j : Fin M, ResetParent (f j) (fatal n) := by
  obtain ⟨n,hn,hres,hdiv⟩ := fatal_high_val_above_four N (3*M)
  exact ⟨n,hn,hres,many_distinct_reset_parents (fatal n) M hdiv⟩

theorem fatal_unbounded_odd_fanin_five (N M : Nat) :
    ∃ n, N<n ∧ n%6=5 ∧
      ∃ f : Fin M → Nat, Function.Injective f ∧
        ∀j : Fin M, ResetParent (f j) (fatal n) := by
  obtain ⟨n,hn,hres,hdiv⟩ := fatal_high_val_above_five N (3*M)
  exact ⟨n,hn,hres,many_distinct_reset_parents (fatal n) M hdiv⟩

#print axioms fatal_unbounded_odd_fanin_four
#print axioms fatal_unbounded_odd_fanin_five
end CascadeAgent44
