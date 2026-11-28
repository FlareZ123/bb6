import ValuationCyclic
import SharpValuationPrimitive

namespace ValuationPacking

/-- A primitive periodic valuation schedule is impossible whenever the
    sharp four-adic capacity is overrun. This replaces the old 6J<K gate
    by the kernel-checked 15J<=2K bound. -/
theorem no_primitive_periodic_slope_sharp (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hn : 0 < n)
    (hper : ∀ i : Int, j (i+(n:Int)) = j i)
    (hmin : MinimalPeriod n j)
    (hK : 15 ≤ K)
    (hgap : 2*K < 15*((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum) : False := by
  exact no_primitive_window_sharp K n v j h
    (minimal_period_backward_primitive n j hn hper hmin) hK hgap

/-- Convenient corollary for signed pair words: if K is at most seven
    times the total gap weight J, the sharp capacity forces a contradiction. -/
theorem no_primitive_periodic_slope_seven (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hn : 0 < n)
    (hper : ∀ i : Int, j (i+(n:Int)) = j i)
    (hmin : MinimalPeriod n j)
    (hK : 15 ≤ K)
    (hJ : 0 < ((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum)
    (hseven : K ≤ 7*((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum) : False := by
  apply no_primitive_periodic_slope_sharp K n v j h hn hper hmin hK
  omega

#print axioms no_primitive_periodic_slope_sharp
#print axioms no_primitive_periodic_slope_seven
end ValuationPacking
