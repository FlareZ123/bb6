import RightFiveDeepCone

namespace BB6.Agent50Shallow
open BB6.Agent28 BB6.Agent47P1 BB6.Agent50DeepCone

/-- Every faithful counted original-source inverse word either contains
    a source-authenticated step of depth zero or one, or belongs to the
    exact all-high-depth grammar. -/
theorem source_shallow_or_all_deep
    (b0 d0 b d m z : Nat)
    (h : CountCone b0 d0 b d m z) :
    (∃ B D M Z t k c,
        CountCone b0 d0 B D M Z ∧
        inverseAt B D t = some (k,c) ∧ t ≤ 1) ∨
      DeepCone b0 d0 b d m := by
  induction h with
  | root => exact Or.inr DeepCone.root
  | parent b d m z t k c hp hb hb4 hd hi hk hc ih =>
    by_cases ht : t ≤ 1
    · exact Or.inl ⟨b,d,m,z,t,k,c,hp,hi,ht⟩
    · rcases ih with hshort | hdeep
      · exact Or.inl hshort
      · exact Or.inr (DeepCone.parent b d m t k c hdeep hb hb4 hd hi hk hc (by omega))

/-- Every original CountCone history ending at the exceptional right-five
    endpoint below the stated mid-cost cap contains an actual t=0 or t=1
    inverseAt transition somewhere in the same genuine source history.
    Reset count and history length are completely unrestricted. -/
theorem source_low_cost_right_five_has_shallow_edge
    (n b m z : Nat) (hn : 14 ≤ n)
    (h : CountCone (14*2^n-2*n-16) 3 b 5 m z)
    (hbudget : 2*m+n+2 ≤ 5*2^n) :
    ∃ B D M Z t k c,
      CountCone (14*2^n-2*n-16) 3 B D M Z ∧
      inverseAt B D t = some (k,c) ∧ t ≤ 1 := by
  rcases source_shallow_or_all_deep _ _ _ _ _ _ h with hshort | hdeep
  · exact hshort
  · have hhigh := deep_cone_right_five_exceeds_mid_cost n b m hn hdeep
    omega

#print axioms BB6.Agent50Shallow.source_shallow_or_all_deep
#print axioms BB6.Agent50Shallow.source_low_cost_right_five_has_shallow_edge

end BB6.Agent50Shallow
