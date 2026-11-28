import SharpValuationCyclic

namespace ValuationPacking
open SharpPackingUniversal

private theorem F_eq_self_lt4 (n : Nat) (h : n<4) : F n=n := by
  rw [F_recur]
  have hq : n/4=0 := by omega
  rw [hq,F_zero]
  omega

private theorem F_four : F 4=5 := by
  rw [F_recur]
  have hq : (4:Nat)/4=1 := by omega
  rw [hq, F_eq_self_lt4 1 (by omega)]

private theorem small_typed_capacity (K J : Nat)
    (hK : 0<K) (hsmall : K<15)
    (hlow : 3*J+2≤K) (hhigh : K+4≤7*J) :
    F ((K-1)/3)-F (K/4)<J := by
  have hb : (K-1)/3≤4 := by omega
  have ha : K/4<4 := by omega
  have hFa : F (K/4)=K/4 := F_eq_self_lt4 (K/4) ha
  by_cases hb4 : (K-1)/3=4
  · rw [hb4,F_four,hFa]
    omega
  · have hblt : (K-1)/3<4 := by omega
    have hFb := F_eq_self_lt4 ((K-1)/3) hblt
    rw [hFb,hFa]
    omega

/-- The typed rank-cost envelope always exceeds exact four-adic capacity. -/
theorem typed_cost_exceeds_capacity (K J : Nat)
    (hK : 0<K)
    (hlow : 3*J+2≤K)
    (hhigh : K+4≤7*J) :
    SharpPackingUniversal.F ((K-1)/3)-SharpPackingUniversal.F (K/4)<J := by
  by_cases h15 : 15≤K
  · have hb := SharpPackingUniversal.sharp_capacity K h15
    omega
  · exact small_typed_capacity K J hK (by omega) hlow hhigh

/-- All-K primitive-cycle obstruction for the rank-cost envelope of a nonempty
    typed E/S word containing a genuine F run. The two arithmetic hypotheses
    abstract exactly T>=3J+2 and T<=7J-4. -/
theorem no_primitive_periodic_slope_typed_cost
    (K n : Nat) (v j : Int → Nat)
    (h : ∀ i : Int, Witness K (v i) (j i) (v (i+1)))
    (hn : 0<n)
    (hper : ∀ i : Int, j (i+(n:Int))=j i)
    (hmin : MinimalPeriod n j)
    (hK : 0<K)
    (hlow : 3*((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum+2≤K)
    (hhigh : K+4≤7*((List.finRange n).map
      (fun s : Fin n => j (s.val:Int))).sum) : False := by
  let J := ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum
  have hprim := minimal_period_backward_primitive n j hn hper hmin
  by_cases h15 : 15≤K
  · apply no_primitive_window_sharp K n v j h hprim h15
    omega
  · have hsmall : K<15 := by omega
    have hcap := primitive_window_exact_capacity K n v j h hprim hK
    have hlt : F ((K-1)/3)-F (K/4)<J := by
      apply small_typed_capacity K J hK hsmall
      · simpa [J] using hlow
      · simpa [J] using hhigh
    change F ((K-1)/3)-F (K/4)<
      ((List.finRange n).map (fun s : Fin n => j (s.val:Int))).sum at hlt
    omega

#print axioms typed_cost_exceeds_capacity
#print axioms no_primitive_periodic_slope_typed_cost
end ValuationPacking
