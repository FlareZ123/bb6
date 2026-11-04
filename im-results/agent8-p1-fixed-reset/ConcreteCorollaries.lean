import SourceBridge
namespace BB6.Agent8Reset
open BB6.Agent28 BB6.Agent1Quarter

theorem budget_mono_count (x k K : Nat) (hx : 0<x) (hle : k≤K) :
    budget x k≤budget x K := by
  induction K generalizing k with
  | zero =>
      have hk : k=0 := by omega
      subst k
      exact Nat.le_refl _
  | succ K ih =>
      by_cases hk : k≤K
      · exact Nat.le_trans (ih k hk) (budget_succ_ge x K hx)
      · have h : k=K+1 := by omega
        subst k
        exact Nat.le_refl _

theorem source_cone_at_least_four_resets_1502
    (b d m : Nat)
    (hcone : OddCone (14*2^1502-2*1502-16) 3 b d m)
    (hwall : b=4*(m+1502)) :
    ∃ z, CountCone (14*2^1502-2*1502-16) 3 b d m z ∧ 4≤z := by
  obtain ⟨z,hz⟩ := odd_cone_has_count _ _ _ _ _ hcone
  refine ⟨z,hz,?_⟩
  by_cases hfour : 4≤z
  · exact hfour
  have hzSmall : z≤3 := by omega
  let x := 1502+2
  let big := budget x 3
  let small := budget x z
  have hbudget : small≤big := budget_mono_count x z 3 (by decide) hzSmall
  have hterms : small*(3*small+3*1502+8) ≤ big*(3*big+3*1502+8) := by
    calc
      _ ≤ small*(3*big+3*1502+8) := Nat.mul_le_mul_left small (by omega)
      _ ≤ big*(3*big+3*1502+8) := Nat.mul_le_mul_right _ hbudget
  have hsmall3 : big*(3*big+3*1502+8) < 7*2^1502 := by decide +kernel
  have hsmallz : budget (1502+2) z*(3*budget (1502+2) z+3*1502+8)<7*2^1502 := by
    change small*(3*small+3*1502+8)<7*2^1502
    exact Nat.lt_of_le_of_lt hterms hsmall3
  exact False.elim (source_counted_no_wall_when_budget_small 1502 b d m z (by decide)
    hz hwall hsmallz)

#print axioms BB6.Agent8Reset.source_cone_at_least_four_resets_1502
end BB6.Agent8Reset
