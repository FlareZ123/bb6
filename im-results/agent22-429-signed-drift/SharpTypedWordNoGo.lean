import SharpTypedCycle
import TypedCostBounds

namespace ValuationPacking

/-- The sharp valuation theorem consumes the actual rank-cost envelope of a
    nonempty typed E/S word with a genuine F-run. The remaining bridge for a
    concrete signed path is to supply the periodic valuation schedule and its
    exponent-sum identity. -/
theorem no_typed_word_primitive_periodic_slope
    (xs : List PeriodicMacro.Letter) (n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness (PeriodicMacro.T xs) (v i) (j i) (v (i+1)))
    (hn : 0<n)
    (hper : ∀ i : Int, j (i+(n:Int))=j i)
    (hmin : MinimalPeriod n j)
    (hsum : ((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum = PeriodicMacro.J xs)
    (hj : ∀ x : PeriodicMacro.Letter, x∈xs → 0<x.j)
    (hne : xs≠[])
    (hlarge : ∃ x : PeriodicMacro.Letter, x∈xs ∧ 1<x.j) : False := by
  cases xs with
  | nil => exact hne rfl
  | cons x tail =>
    have hlow0 := PeriodicMacro.typed_cost_lower x tail hj
    have hhigh0 := PeriodicMacro.typed_cost_upper_strict (x::tail) hj hlarge
    have hK : 0<PeriodicMacro.T (x::tail) := by omega
    apply no_primitive_periodic_slope_typed_cost
      (PeriodicMacro.T (x::tail)) n v j h hn hper hmin hK
    · rw [hsum]
      exact hlow0
    · rw [hsum]
      exact hhigh0

#print axioms no_typed_word_primitive_periodic_slope
end ValuationPacking
