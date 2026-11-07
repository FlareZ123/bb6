import NeedleQuarticEnumerate
import FifthHigh
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace NeedleQuinticEnum
open NeedleInverse

/-- The exact all-natural valuation ceiling from the former fourth-linear
    theorem, now with the fifth-linear bound and two isolated exceptions. -/
theorem quintic_valuation_bound (q v K : Nat) (h : equation q v K) :
    (q=61 ∧ v=6 ∧ K=13) ∨
    (q=340282366920822406584691642613415018481 ∧ v=42 ∧ K=171) ∨
    5*v≤K+3 := by
  rcases NeedleQuarticEnum.quartic_valuation_bound q v K h with hex | h4
  · exact Or.inl hex
  · right
    have hmodel : BB6.Agent48.FifthHigh.equation q v K := by
      unfold BB6.Agent48.FifthHigh.equation BB6.Agent48.FifthHigh.den BB6.Agent48.FifthHigh.bias
      change BB6.Agent48.Boundary.den v*q+BB6.Agent48.Boundary.bias v = (2:Nat)^K
      rw [BB6.Agent48.Boundary.model_eq]
      exact h
    exact BB6.Agent48.FifthHigh.fifth_exact q v K hmodel h4

/-- All one-step terminal feeders using only floor((K+3)/5)+1 ordinary
    valuations, plus the unique small and fourth-power exceptions. -/
def quinticParents (K : Nat) : List (Nat × Nat) :=
  (if K=13 then [(6,61)] else []) ++
  (if K=171 then [(42,340282366920822406584691642613415018481)] else []) ++
  (List.range ((K+3)/5+1)).filterMap fun v =>
    (candidate v K).map fun q => (v,q)

/-- An exact unbounded iff, with no finite terminal-exponent limit. -/
theorem quinticParents_spec (q v K : Nat) :
    (v,q) ∈ quinticParents K ↔ equation q v K := by
  constructor
  · intro hm
    have hor : (v,q) ∈ (if K=13 then [(6,61)] else []) ∨
        (v,q) ∈ (if K=171 then [(42,340282366920822406584691642613415018481)] else []) ∨
        (v,q) ∈ (List.range ((K+3)/5+1)).filterMap
          (fun v => (candidate v K).map fun q => (v,q)) := by
      simpa only [quinticParents, List.mem_append, or_assoc] using hm
    rcases hor with h13 | h171 | hbase
    · by_cases hk : K=13
      · simp [hk] at h13
        rcases h13 with ⟨hv,hq⟩
        subst v
        subst q
        subst K
        unfold equation
        decide
      · simp [hk] at h13
    · by_cases hk : K=171
      · simp [hk] at h171
        rcases h171 with ⟨hv,hq⟩
        subst v
        subst q
        subst K
        unfold equation
        decide
      · simp [hk] at h171
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
    have hb := quintic_valuation_bound q v K heq
    apply List.mem_append.mpr
    rcases hb with ⟨hq,hv,hK⟩ | ⟨hq,hv,hK⟩ | hbound
    · left
      apply List.mem_append.mpr
      left
      subst q
      subst v
      subst K
      simp
    · left
      apply List.mem_append.mpr
      right
      subst q
      subst v
      subst K
      simp
    · right
      apply List.mem_filterMap.mpr
      have hvdiv : v ≤ (K+3)/5 :=
        (Nat.le_div_iff_mul_le (by decide : 0<(5:Nat))).mpr (by omega)
      refine ⟨v,List.mem_range.mpr (by omega),?_⟩
      simp [(candidate_correct q v K).mpr heq]

#print axioms quintic_valuation_bound
#print axioms quinticParents_spec
end NeedleQuinticEnum
