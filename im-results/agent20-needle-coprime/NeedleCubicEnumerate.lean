import NeedleCubicBound
import Lean.Elab.Tactic.Omega

namespace NeedleCubicEnum
open NeedleInverse

/-- Exhaustive terminal inverse enumeration with at most (K+2)/3+1
ordinary valuation candidates and one isolated exceptional feeder. -/
def cubicParents (K : Nat) : List (Nat × Nat) :=
  (if K=13 then [(6,61)] else []) ++
    (List.range ((K+2)/3+1)).filterMap fun v =>
      (candidate v K).map fun q => (v,q)

theorem cubicParents_spec (q v K : Nat) :
    (v,q) ∈ cubicParents K ↔ equation q v K := by
  constructor
  · intro hm
    have hor : (v,q) ∈ (if K=13 then [(6,61)] else []) ∨
      (v,q) ∈ (List.range ((K+2)/3+1)).filterMap
        (fun v => (candidate v K).map fun q => (v,q)) := by
      simpa only [cubicParents, List.mem_append] using hm
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
      cases hc : candidate v' K with
      | none => simp [hc] at hmap
      | some q' =>
        have hp : (v',q')=(v,q) := by simpa [hc] using hmap
        obtain ⟨hv,hq⟩ := Prod.mk.inj hp
        subst v'
        subst q'
        exact (candidate_correct q v K).mp hc
  · intro heq
    have hb := NeedleCubicBound.cubic_valuation_bound q v K heq
    apply List.mem_append.mpr
    rcases hb with ⟨hq,hv,hK⟩ | hbound
    · left
      subst q
      subst v
      subst K
      simp
    · right
      apply List.mem_filterMap.mpr
      have hvdiv : v ≤ (K+2)/3 :=
        (Nat.le_div_iff_mul_le (by decide : 0<(3:Nat))).mpr (by omega)
      refine ⟨v, List.mem_range.mpr (by omega), ?_⟩
      simp [(candidate_correct q v K).mpr heq]

#eval cubicParents 9
#eval cubicParents 12
#eval cubicParents 13
#eval cubicParents 40
#print axioms cubicParents_spec
end NeedleCubicEnum
