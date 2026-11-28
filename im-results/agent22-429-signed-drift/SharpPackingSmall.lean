import Std

/-!
Lean kernel certificate for the 136 finite small-K base cases of the
sharp signed valuation packing theorem (15 <= K <= 150).
The infinite-range argument and upper-quotient injection are separate.
For K <= 150, b=(K-1)/3 <= 49 and a=K/4 <=37, so
F(b)=b+b/4+b/16 and F(a)=a+a/4+a/16 exactly.
-/
namespace SharpPackingSmall

def truncatedF (n : Nat) : Nat := n+n/4+n/16

def capacity (K : Nat) : Nat :=
  truncatedF ((K-1)/3)-truncatedF (K/4)

/-- Exact exhaustive 136-case arithmetic base for 15*capacity <= 2*K. -/
theorem small_range_fin :
    ∀ k : Fin 151, 15 ≤ k.val →
      15*capacity k.val ≤ 2*k.val := by decide

theorem small_range (K : Nat)
    (hlo : 15 ≤ K) (hhi : K ≤ 150) :
    15*capacity K ≤ 2*K := by
  exact small_range_fin ⟨K, by omega⟩ hlo

theorem sharp_at_15 : capacity 15=2 := by decide

#print axioms small_range_fin
#print axioms small_range
#print axioms sharp_at_15
end SharpPackingSmall
