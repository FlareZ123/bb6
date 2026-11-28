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

/-- The exact capacity improves to coefficient 8 from K=64 onward. -/
theorem eight_from_sixty_four :
    ∀ K : Nat, 64≤K → ∀ es : List (Edge K),
      (es.map (fun e => e.v)).Nodup →
      8*(es.map (fun e => e.j)).sum≤K := by
  intro K hK es hn
  have hc := exact_edge_family_capacity K es (by omega) hn
  have hb := SharpPackingUniversal.sharp_eight K hK
  omega

/-- K=63 is the last obstruction to the uniform coefficient-8 bound. -/
theorem factor_eight_fails_at_63 :
    ∃ es : List (Edge 63),
      (es.map (fun e => e.v)).Nodup ∧
      63 < 8*(es.map (fun e => e.j)).sum := by
  refine ⟨exactMaxEdges 63,exactMaxEdges_v_nodup 63,?_⟩
  have hs := exactMaxEdges_j_sum 63
  have hb : (63-1)/3=20 := by omega
  have ha : 63/4=15 := by omega
  have h20 : SharpPackingUniversal.F 20=26 := by
    rw [SharpPackingUniversal.F_three_of_lt64 20 (by omega)]
  have h15 : SharpPackingUniversal.F 15=18 := by
    rw [SharpPackingUniversal.F_three_of_lt64 15 (by omega)]
  rw [hb,ha,h20,h15] at hs
  omega

#print axioms eight_from_sixty_four
#print axioms factor_eight_fails_at_63
end ValuationPacking
