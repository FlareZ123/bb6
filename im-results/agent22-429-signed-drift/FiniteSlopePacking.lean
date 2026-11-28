import FinitePowerSlopeCycle
import SharpValuationFamily
import TypedCostBounds
import SharpTypedCycle

namespace PeriodicMacro
open ValuationPacking

private theorem slope_step_propagates_cone {x : Letter} {K d e : Nat}
    (hj : 0<x.j) (heq : scale x*e=d+K)
    (hd : 0<d) (hcone : 3*d<K) :
    0<e ∧ 3*e<K := by
  have hs : 4≤scale x := scale_ge_four x hj
  have hepos : 0<e := by
    by_cases hz : e=0
    · subst e
      simp at heq
      omega
    · exact Nat.pos_of_ne_zero hz
  have h4 : 4*e≤d+K := by
    have hm := Nat.mul_le_mul_right e hs
    rw [heq] at hm
    simpa [Nat.mul_comm] using hm
  constructor
  · exact hepos
  · omega

inductive SlopeWalkSources (K : Nat) :
    List Letter → List Nat → Nat → Nat → Prop where
  | nil (d : Nat) : SlopeWalkSources K [] [] d d
  | cons {x : Letter} {xs : List Letter} {ds : List Nat}
      {d e f : Nat} (head : scale x*e=d+K)
      (tail : SlopeWalkSources K xs ds e f) :
      SlopeWalkSources K (x::xs) (d::ds) d f

theorem slopeWalk_sources_exists {K : Nat} {xs : List Letter} {d f : Nat}
    (h : SlopeWalk K xs d f) :
    ∃ ds : List Nat, SlopeWalkSources K xs ds d f := by
  induction h with
  | nil d => exact ⟨[],SlopeWalkSources.nil d⟩
  | cons head tail ih =>
      obtain ⟨ds,hds⟩ := ih
      exact ⟨_::ds,SlopeWalkSources.cons head hds⟩

theorem slopeWalkSources_edges {K : Nat} {xs : List Letter}
    {ds : List Nat} {d f : Nat}
    (h : SlopeWalkSources K xs ds d f)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hd : 0<d) (hcone : 3*d<K) :
    ∃ es : List (Edge K),
      es.map (fun e => e.v)=ds ∧
      (es.map (fun e => e.j)).sum=J xs := by
  induction h with
  | nil d => exact ⟨[],by simp,by simp [J]⟩
  | @cons x xs ds d e f heq tail ih =>
      have hxj : 0<x.j := hj x (by simp)
      have hjtail : ∀ y : Letter, y∈xs → 0<y.j := by
        intro y hy
        exact hj y (by simp [hy])
      have hnext := slope_step_propagates_cone hxj heq hd hcone
      obtain ⟨es,hvs,hjs⟩ := ih hjtail hnext.1 hnext.2
      let headEdge : Edge K := {
        v:=d, j:=x.j, next:=e,
        vpos:=hd, vsmall:=hcone, jpos:=hxj,
        eqn:=by simpa [scale] using heq }
      refine ⟨headEdge::es,?_,?_⟩
      · change d :: es.map (fun e => e.v) = d :: ds
        rw [hvs]
      · change x.j+(es.map (fun e => e.j)).sum=x.j+J xs
        rw [hjs]

/-- Finite capacity theorem for a strict-cone slope walk whose explicitly
    indexed source slopes are distinct. -/
theorem slopeWalkSources_exact_capacity {K : Nat} {xs : List Letter}
    {ds : List Nat} {d f : Nat}
    (h : SlopeWalkSources K xs ds d f)
    (hj : ∀ x : Letter, x∈xs → 0<x.j)
    (hd : 0<d) (hcone : 3*d<K)
    (hn : ds.Nodup) :
    J xs ≤ SharpPackingUniversal.F ((K-1)/3)-SharpPackingUniversal.F (K/4) := by
  have hK : 0<K := by omega
  obtain ⟨es,hvs,hjs⟩ := slopeWalkSources_edges h hj hd hcone
  have hnodup : (es.map (fun e => e.v)).Nodup := by rwa [hvs]
  have hb := exact_edge_family_capacity K es hK hnodup
  rwa [hjs] at hb

/-- Once a typed strict slope cycle has pairwise distinct finite source slopes,
    the exact four-adic capacity contradicts the real E/S rank-cost envelope. -/
theorem no_distinct_typed_slope_cycle
    (x : Letter) (xs : List Letter) {ds : List Nat} {d : Nat}
    (h : SlopeWalkSources (T (x::xs)) (x::xs) ds d d)
    (hj : ∀ y : Letter, y∈x::xs → 0<y.j)
    (hlarge : ∃ y : Letter, y∈x::xs ∧ 1<y.j)
    (hd : 0<d) (hcone : 3*d<T (x::xs))
    (hn : ds.Nodup) : False := by
  have hcap := slopeWalkSources_exact_capacity h hj hd hcone hn
  have hlow := typed_cost_lower x xs hj
  have hhigh := typed_cost_upper_strict (x::xs) hj hlarge
  have hK : 0<T (x::xs) := by omega
  have hexceed := ValuationPacking.typed_cost_exceeds_capacity
    (T (x::xs)) (J (x::xs)) hK hlow hhigh
  omega

#print axioms slopeWalkSources_edges
#print axioms slopeWalkSources_exact_capacity
#print axioms no_distinct_typed_slope_cycle
end PeriodicMacro
