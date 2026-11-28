import SlopeCycleAdapter

namespace PeriodicMacro
open FiniteCyclicValuation

/-- A primitive typed strict slope cycle containing a genuine F run is
    impossible by exact four-adic capacity. -/
theorem no_primitive_typed_slope_cycle
    (x : Letter) (xs : List Letter) {ds : List Nat} {d : Nat}
    (h : SlopeWalkSources (T (x::xs)) (x::xs) ds d d)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j)
    (hd : 0<d) (hcone : 3*d<T (x::xs))
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (slopeExponentFun (x::xs))) : False := by
  have hn := closedSlope_sources_nodup h hj hd hcone (by simp) hprim
  exact no_distinct_typed_slope_cycle x xs h hj hlarge hd hcone hn

/-- Fully finite primitive-power obstruction: once the exact power-rigidity
    threshold is crossed, a nonempty primitive positive-j typed word containing
    a genuine F run cannot repeat the required number of times. -/
theorem no_primitive_finite_power
    (x : Letter) (xs : List Letter) (u r : Nat → Nat) (n : Nat)
    (hw : ∀ i : Nat, i≤n+1 →
      Walk (x::xs) (u i) (r i) (u (i+1)) (r (i+1)))
    (hsafe0 : 3*u 0≤r 0)
    (hsafe1 : 3*u 1≤r 1)
    (hsafe2 : 3*u 2≤r 2)
    (hbig : 2*((r 0+2*T (x::xs))/3)<(M (x::xs))^n)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j)
    (hprim : CyclicPrimitive (by simp : 0<(x::xs).length)
      (slopeExponentFun (x::xs))) : False := by
  obtain ⟨d,hd,hcone,hcycle⟩ :=
    finite_power_gives_strict_slope_cycle x xs u r n hw
      hsafe0 hsafe1 hsafe2 hbig hj hlarge
  obtain ⟨ds,hds⟩ := slopeWalk_sources_exists hcycle
  exact no_primitive_typed_slope_cycle x xs hds hj hlarge hd hcone hprim

#print axioms no_primitive_typed_slope_cycle
#print axioms no_primitive_finite_power
end PeriodicMacro
