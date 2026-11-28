import SharpExactValuation
import SharpWitness

namespace ValuationPacking

/-- Canonical kernel statement of the globally sharp 15/2 coefficient:
    every legal distinct-source family satisfies it for K>=15, and equality
    occurs at K=15. -/
theorem sharp_fifteen_halves_optimal :
    (∀ K : Nat, 15≤K → ∀ es : List (Edge K),
      (es.map (fun e => e.v)).Nodup →
      15*(es.map (fun e => e.j)).sum≤2*K) ∧
    (∃ K : Nat, 15≤K ∧ ∃ es : List (Edge K),
      (es.map (fun e => e.v)).Nodup ∧
      15*(es.map (fun e => e.j)).sum=2*K) := by
  constructor
  · intro K hK es hn
    exact sharp_edge_family_budget K es hK hn
  · exact ⟨15,by omega,[sharp15Edge],sharp15_family_nodup,sharp15_equality⟩

/-- The exact per-K extremal formula and the sharp uniform 15/2 coefficient
    are simultaneously available in the canonical valuation edge model. -/
theorem exact_and_sharp_capacity (K : Nat) (hK : 0<K) :
    ((∀ es : List (Edge K), (es.map (fun e => e.v)).Nodup →
        (es.map (fun e => e.j)).sum ≤
          SharpPackingUniversal.F ((K-1)/3)-SharpPackingUniversal.F (K/4)) ∧
      (∃ es : List (Edge K), (es.map (fun e => e.v)).Nodup ∧
        (es.map (fun e => e.j)).sum =
          SharpPackingUniversal.F ((K-1)/3)-SharpPackingUniversal.F (K/4))) :=
  exact_capacity_characterization K hK

#print axioms sharp_fifteen_halves_optimal
#print axioms exact_and_sharp_capacity
end ValuationPacking
