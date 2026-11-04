import ChainWitnesses
import SheepGenericConverse

namespace Audit

/-- Both displayed arrows are original-source Sheep even-section returns.
Completeness of the inverse cone is a separate theorem, not asserted here. -/
theorem chain402_source (k : Nat) :
    ∃ A B : Nat,
      SheepEven.EvenEdge A (2^(402+4860*k)) ∧
      SheepEven.EvenEdge B A ∧
      15*A+2=8*2^(402+4860*k) ∧
      1485*B+4688=512*2^(402+4860*k) ∧
      10 < B ∧ B < A ∧ A < 2^(402+4860*k) := by
  obtain ⟨A,B,hA,hB,heqA,heqB,h10,hBA,hAR⟩ := chain402 k
  exact ⟨A,B,
    SheepGenericConverse.generic_to_source hA,
    SheepGenericConverse.generic_to_source hB,
    heqA,heqB,h10,hBA,hAR⟩

/-- The 1738 chain has the same original-source semantics. -/
theorem chain1738_source (k : Nat) :
    ∃ A B : Nat,
      SheepEven.EvenEdge A (2^(1738+4860*k)) ∧
      SheepEven.EvenEdge B A ∧
      15*A+2=8*2^(1738+4860*k) ∧
      135*B+196=64*2^(1738+4860*k) ∧
      10 < B ∧ B < A ∧ A < 2^(1738+4860*k) := by
  obtain ⟨A,B,hA,hB,heqA,heqB,h10,hBA,hAR⟩ := chain1738 k
  exact ⟨A,B,
    SheepGenericConverse.generic_to_source hA,
    SheepGenericConverse.generic_to_source hB,
    heqA,heqB,h10,hBA,hAR⟩

#print axioms chain402_source
#print axioms chain1738_source

end Audit
