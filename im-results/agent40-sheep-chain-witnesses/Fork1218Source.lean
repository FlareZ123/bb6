import Fork1218
import SheepGenericConverse

namespace Audit

/-- Source-level existence of the two distinct r1218 fork parents.
This does not assert that all other even-section parents are impossible. -/
theorem fork1218_source (k : Nat) :
    ∃ A B : Nat,
      SheepEven.EvenEdge A (2^(1218+4860*k)) ∧
      SheepEven.EvenEdge B (2^(1218+4860*k)) ∧
      A ≠ B ∧ 15*A+2=8*2^(1218+4860*k) ∧
      81*B+68=32*2^(1218+4860*k) ∧
      10 < A ∧ A < 2^(1218+4860*k) ∧
      10 < B ∧ B < 2^(1218+4860*k) := by
  obtain ⟨A,B,hA,hB,hne,heqA,heqB,h10A,hAR,h10B,hBR⟩ := fork1218 k
  exact ⟨A,B,
    SheepGenericConverse.generic_to_source hA,
    SheepGenericConverse.generic_to_source hB,
    hne,heqA,heqB,h10A,hAR,h10B,hBR⟩

#print axioms fork1218_source
end Audit
