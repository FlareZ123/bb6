import NeedleSharper
import OffsetStrip
import Lean.Elab.Tactic.Omega

namespace NeedleQuarticEnum
open NeedleInverse

/-- A complete fourth-linear bound on the valuation of a terminal predecessor. -/
theorem quartic_valuation_bound (q v K : Nat) (h : equation q v K) :
    (q=61 ∧ v=6 ∧ K=13) ∨ 4*v ≤ K+2 := by
  rcases NeedleSharper.sharper_valuation_bound q v K h with hex | hsharp
  · exact Or.inl hex
  · right
    have hmodel : BB6.Agent48.Boundary.equation q v K := by
      unfold BB6.Agent48.Boundary.equation
      rw [BB6.Agent48.Boundary.model_eq]
      exact h
    exact BB6.Agent48.OffsetStrip.stronger_from_sharp q v K hmodel hsharp

/-- Exhaustive terminal inverse search using only (K+2)/4+1 valuation
candidates, together with the unique isolated exception (v,q,K)=(6,61,13). -/
def quarticParents (K : Nat) : List (Nat × Nat) :=
  (if K=13 then [(6,61)] else []) ++
    (List.range ((K+2)/4+1)).filterMap fun v =>
      (candidate v K).map fun q => (v,q)

/-- Exact, unbounded correctness of the fourth-linear inverse enumeration. -/
theorem quarticParents_spec (q v K : Nat) :
    (v,q) ∈ quarticParents K ↔ equation q v K := by
  constructor
  · intro hm
    have hor : (v,q) ∈ (if K=13 then [(6,61)] else []) ∨
        (v,q) ∈ (List.range ((K+2)/4+1)).filterMap
          (fun v => (candidate v K).map fun q => (v,q)) := by
      simpa only [quarticParents, List.mem_append] using hm
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
      have hvdiv : v ≤ (K+2)/4 :=
        (Nat.le_div_iff_mul_le (by decide : 0<(4:Nat))).mpr (by omega)
      refine ⟨v, List.mem_range.mpr (by omega), ?_⟩
      simp [(candidate_correct q v K).mpr heq]

#eval quarticParents 9
#eval quarticParents 12
#eval quarticParents 13
#eval quarticParents 40
#print axioms quartic_valuation_bound
#print axioms quarticParents_spec
end NeedleQuarticEnum
