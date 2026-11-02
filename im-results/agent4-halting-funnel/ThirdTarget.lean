import NoSecondTarget
namespace BB6.HaltingFunnel

/-- The third critical target is reachable exactly when the odd-sector
    gateway (36,3) is reached. The alternative 38,2 reset is ruled out
    by the global modular invariant. -/
theorem third_critical_iff_gateway :
    BlankReach 2 42 ↔ BlankReach 36 3 := by
  constructor
  · intro h
    cases h with
    | next a c _ _ hpre ht =>
        obtain ⟨ha,hc⟩ := T_to_two_positive a c 42 (by decide) ht
        have ha41 : a=41 := by omega
        subst a
        subst c
        cases hpre with
        | next a c _ _ hpre2 ht2 =>
            rcases T_odd_left_predecessor a c 41 0 ht2 (by decide) with h39 | h38
            · obtain ⟨hc,hb,hd⟩ := h39
              have ha39 : a=39 := by omega
              subst a
              subst c
              cases hpre2 with
              | next a c _ _ hpre3 ht3 =>
                  rcases T_odd_left_predecessor a c 39 1 ht3 (by decide) with h | h
                  · omega
                  · obtain ⟨ha,hbound,hb,hd⟩ := h
                    have ha36 : a=36 := by omega
                    have hc3 : c=3 := by omega
                    subst a
                    subst c
                    exact hpre3
            · obtain ⟨ha,hbound,hb,hd⟩ := h38
              have ha38 : a=38 := by omega
              have hc2 : c=2 := by omega
              subst a
              subst c
              have hinv := blank_even_left_invariant 38 2 hpre2 (by decide) (by decide)
              rcases hinv with h | h <;> omega
  · intro h
    have ht1 : T 36 3 = some (39,1) := by decide
    have ht2 : T 39 1 = some (41,0) := by decide
    have ht3 : T 41 0 = some (2,42) := by decide
    exact BlankReach.next 41 0 2 42
      (BlankReach.next 39 1 41 0
      (BlankReach.next 36 3 39 1 h ht1) ht2) ht3

#print axioms BB6.HaltingFunnel.third_critical_iff_gateway
end BB6.HaltingFunnel
