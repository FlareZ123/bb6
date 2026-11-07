import BlankParam
import M8M16Composition
import M192GeneralBound
import SmallSecondFamily

namespace BB6.Agent15

/-- The M192 source invariant eliminates every large-right-coordinate
section target. The remaining two small parameter points are excluded by
the original CLine rank invariant and Agent 6's independent finite feeder
certificate. Consequently Machine C cannot halt from blank. -/
theorem blank_machine_c_never_halts :
    ¬ BB6.CReachBridge.RunHalts := by
  intro hhalt
  have hparam := (blank_halts_iff_two_parametric_families).mp hhalt
  rcases hparam with ⟨time, a, k, hr, hfamily⟩
  rcases hfamily with hfirst | hsecond
  · rcases hfirst with ⟨ha, m, heq⟩
    subst a
    by_cases hm0 : m=0
    · subst m
      have heq' : k+4=8 := by simpa using heq
      have hk4 : k=4 := by omega
      subst k
      have hC : CReach 1 4 := ⟨time, hr⟩
      have hline := section_reach_embeds hC
      have hne := BB6CLine.special_unreachable (1,4,0) hline
      exact hne rfl
    · have hmpos : 1≤m := by omega
      have hkge8 := first_stop_k_ge8 m k hmpos heq
      have hC : CReach 1 k := ⟨time, hr⟩
      exact source_no_c0_right_ge8 1 k hkge8 (section_reach_embeds hC)
  · rcases hsecond with ⟨j, m, ha, heq⟩
    subst a
    by_cases hsmall : j=0 ∧ m=0
    · rcases hsmall with ⟨rfl, rfl⟩
      have heq' : k+5=12 := by simpa using heq
      have hk7 : k=7 := by omega
      subst k
      have hC : CReach 3 7 := ⟨time, hr⟩
      exact source_no_3_7 (section_reach_embeds hC)
    · have hjm : j ≠ 0 ∨ m ≠ 0 := by
        by_cases hj0 : j=0
        · right
          intro hm0
          exact hsmall ⟨hj0, hm0⟩
        · exact Or.inl hj0
      have hC : CReach (2*j+3) k := ⟨time, hr⟩
      exact source_no_second_stop_except_00 j m k hjm heq
        (section_reach_embeds hC)

#print axioms blank_machine_c_never_halts

end BB6.Agent15
