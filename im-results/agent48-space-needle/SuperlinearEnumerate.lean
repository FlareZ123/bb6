import SuperlinearAll
import NeedleQuarticEnumerate

namespace BB6.Agent48.SuperlinearEnum
open NeedleInverse
open NeedleQuarticEnum
open BB6.Agent48.SuperMod

/-- Any admissible terminal feeder has a valuation below the flexible
all-slope cutoff, for arbitrary positive slope c. -/
theorem all_slope_valuation_cutoff (q v K c : Nat)
    (hc : 1≤c) (he : equation q v K) :
    v < max (4*((3:Nat)^c+1)) (K/c+1) := by
  by_cases hv : v < 4*((3:Nat)^c+1)
  · have hmax := Nat.le_max_left (4*((3:Nat)^c+1)) (K/c+1)
    omega
  · have hvbound : 4*((3:Nat)^c+1)≤v := by omega
    have hs : c*v<K := terminal_superlinear_nat q v K c hc hvbound he
    have hdiv : v≤K/c := by
      apply (Nat.le_div_iff_mul_le (by omega : 0<c)).mpr
      have hmul : v*c=c*v := by ac_rfl
      rw [hmul]
      omega
    have hmax := Nat.le_max_right (4*((3:Nat)^c+1)) (K/c+1)
    omega

/-- Complete exact candidate enumeration with a flexible superlinear cutoff.
The candidate set is the intersection of the quarter-linear candidate range
and an all-slope range, plus the exact isolated (6,61,K13) exception. -/
def superlinearParents (K c : Nat) : List (Nat × Nat) :=
  (if K=13 then [(6,61)] else []) ++
    (List.range (min ((K+2)/4+1) (max (4*((3:Nat)^c+1)) (K/c+1)))).filterMap
      fun v => (candidate v K).map fun q => (v,q)

/-- All-natural exact iff for the combined quartic/superlinear enumeration. -/
theorem superlinearParents_spec (q v K c : Nat) (hc : 1≤c) :
    (v,q) ∈ superlinearParents K c ↔ equation q v K := by
  constructor
  · intro hm
    have hor : (v,q) ∈ (if K=13 then [(6,61)] else []) ∨
        (v,q) ∈ (List.range (min ((K+2)/4+1) (max (4*((3:Nat)^c+1)) (K/c+1)))).filterMap
          (fun v => (candidate v K).map fun q => (v,q)) := by
      simpa only [superlinearParents, List.mem_append] using hm
    rcases hor with hspecial | hbase
    · by_cases hk : K=13
      · simp [hk] at hspecial
        rcases hspecial with ⟨hv,hq⟩
        subst v
        subst q
        subst K
        decide
      · simp [hk] at hspecial
    · obtain ⟨v',hsize,hmap⟩ := List.mem_filterMap.mp hbase
      cases hcand : candidate v' K with
      | none => simp [hcand] at hmap
      | some q' =>
        have hp : (v',q')=(v,q) := by simpa [hcand] using hmap
        obtain ⟨hv,hq⟩ := Prod.mk.inj hp
        subst v'
        subst q'
        exact (candidate_correct q v K).mp hcand
  · intro heq
    have hb := quartic_valuation_bound q v K heq
    apply List.mem_append.mpr
    rcases hb with ⟨hq,hv,hK⟩ | hbound
    · left
      subst q
      subst v
      subst K
      simp
    · right
      apply List.mem_filterMap.mpr
      have h1 : v ≤ (K+2)/4 :=
        (Nat.le_div_iff_mul_le (by decide : 0<(4:Nat))).mpr (by omega)
      have h2 := all_slope_valuation_cutoff q v K c hc heq
      have hmin : v < min ((K+2)/4+1) (max (4*((3:Nat)^c+1)) (K/c+1)) := by
        exact Nat.lt_min.mpr ⟨by omega,h2⟩
      refine ⟨v, List.mem_range.mpr hmin, ?_⟩
      simp [(candidate_correct q v K).mpr heq]

#print axioms all_slope_valuation_cutoff
#print axioms superlinearParents_spec
end BB6.Agent48.SuperlinearEnum
