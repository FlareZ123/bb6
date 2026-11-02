import AffineQuotientExclusion

namespace BB6.Agent15

private theorem case_yes : affineQuotientExcluded 19 720862 = true := by
  have hn : affineNormalize 19 720862 = (1351623,45052) := by
    simp [affineNormalize]
  simp [affineQuotientExcluded,affineExcluded,affineQuotientCondition,hn]

private theorem case_no : affineQuotientExcluded 19 3096224743817134 = false := by
  have hn : affineNormalize 19 3096224743817134 =
      (5418393301679995,387028092977140) := by
    simp [affineNormalize]
  simp [affineQuotientExcluded,affineExcluded,affineQuotientCondition,hn]

/-- A kernel-checkable counterexample to the conjecture that the filter on
the second halting family depends only on j and m modulo 16. The two
halting-parameter indices are j=8, m=7 and m=23, and both satisfy
the same j,m residue pair. Their executable filter decisions differ.
This says nothing about either state's actual blank reachability. -/
theorem second_filter_not_periodic_mod16 :
  ∃ j m₁ m₂ k₁ k₂ : Nat,
    m₁%16=m₂%16 ∧ m₁≠m₂ ∧
    k₁+j+3*m₁+5=2^(2*m₁+2)*(j+3) ∧
    k₂+j+3*m₂+5=2^(2*m₂+2)*(j+3) ∧
    affineQuotientExcluded (2*j+3) k₁ = true ∧
    affineQuotientExcluded (2*j+3) k₂ = false := by
  refine ⟨8,7,23,720862,3096224743817134, by decide, by decide,
    by decide, by decide, ?_, ?_⟩
  · exact case_yes
  · exact case_no

#print axioms second_filter_not_periodic_mod16
end BB6.Agent15
