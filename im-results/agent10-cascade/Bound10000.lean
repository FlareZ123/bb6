import Cert10000
namespace CascadeResetShield

theorem no_fatal_through_10000 (n : Nat) (hn : n≤10000) :
    ¬ Path Edge 2 (fatal n) := by
  obtain ⟨z,hp,hz⟩ := certified_prefix_10000
  exact bounded_fatal_exclusion edge_deterministic edge_strict (fun _ _ h => h)
    10000 z hp hz n hn

#print axioms no_fatal_through_10000
end CascadeResetShield
