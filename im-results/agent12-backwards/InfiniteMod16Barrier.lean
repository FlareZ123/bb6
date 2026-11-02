import NoFourthTarget

namespace BB6.Agent12

/-- Every sufficiently large multiple of 16 on the right is forbidden
    at left counter 2 in the actual blank-entry orbit. -/
theorem blank_no_zero_mod_sixteen (d : Nat) (hlarge:64≤d) (hmod:d%16=0) :
    ¬BlankReach 2 d := by
  intro hr
  cases hr with
  | init => omega
  | next a c _ _ hpre ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c d (by omega) ht
      have haodd : a%2=1 := by omega
      cases hpre with
      | init => omega
      | next x y _ _ hpre2 ht2 =>
          rcases T_odd_left_predecessor x y a c ht2 haodd with hfirst | hsecond
          · obtain ⟨hy,hb,hd⟩ := hfirst
            have hxodd : x%2=1 := by omega
            cases hpre2 with
            | init => omega
            | next u v _ _ hpre3 ht3 =>
                rcases T_odd_left_predecessor u v x y ht3 hxodd with hh | hh
                · omega
                · obtain ⟨hu,hv,hb',hd'⟩ := hh
                  have hinv:=blank_even_left_invariant u v hpre3 (by omega) hu
                  rcases hinv with h | h <;> omega
          · obtain ⟨hx,hy,hb,hd⟩ := hsecond
            have hxmod : x%4=0 := by omega
            have hypos:0<y := by omega
            have hymod:y%2=0 := by omega
            cases hpre2 with
            | init => omega
            | next z t _ _ hpre3 ht3 =>
                obtain ⟨hz,ht⟩ := T_to_mult4_even z t x y ht3 hxmod hymod hypos
                have hzodd:z%2=1 := by omega
                cases hpre3 with
                | init => omega
                | next u v _ _ hpre4 ht4 =>
                    rcases T_odd_left_predecessor u v z t ht4 hzodd with hh | hh
                    · omega
                    · obtain ⟨hu,hv,hb',hd'⟩ := hh
                      have humod:u%4=0 := by omega
                      have hvpos:0<v := by omega
                      have hvmod:v%2=0 := by omega
                      cases hpre4 with
                      | init => omega
                      | next w r _ _ hpre5 ht5 =>
                          obtain ⟨hw,hr⟩ := T_to_mult4_even w r u v ht5 humod hvmod hvpos
                          have hwodd:w%2=1 := by omega
                          cases hpre5 with
                          | init => omega
                          | next p q _ _ hpre6 ht6 =>
                              rcases T_odd_left_predecessor p q w r ht6 hwodd with hh | hh
                              · omega
                              · obtain ⟨hp,hq,hb'',hd''⟩ := hh
                                have hinv:=blank_even_left_invariant p q hpre6 (by omega) hp
                                rcases hinv with h | h <;> omega

#print axioms BB6.Agent12.blank_no_zero_mod_sixteen

#print axioms BB6.Agent12.blank_no_critical_one_mod_four

#print axioms BB6.Agent12.blank_no_four_mod_eight

/-- Infinite additional critical halting-target subfamily:
    n>=3 and n=3 mod 8; includes n=3 target 96. -/
theorem blank_no_critical_three_mod_eight (n : Nat)
    (hn : 3≤n) (hnmod:n%8=3) :
    ¬BlankReach 2 (14*2^n - 2*n - 10) := by
  by_cases h3 : n=3
  · subst n
    exact blank_no_zero_mod_sixteen 96 (by decide) (by decide)
  · have hn11 : 11≤n := by omega
    have hpowbound : ∀ j:Nat, j+1≤2^j := by
      intro j
      induction j with
      | zero => decide
      | succ j ih =>
        rw [Nat.pow_succ]
        omega
    have hsize:=hpowbound n
    have hlarge : 64≤14*2^n - 2*n - 10 := by omega
    have hpowmod : (2^n)%16=0 := by
      have h4:n=n-4+4 := by omega
      rw [h4, Nat.pow_add]
      simp
    have hmod : (14*2^n - 2*n - 10)%16=0 := by omega
    exact blank_no_zero_mod_sixteen _ hlarge hmod

#print axioms BB6.Agent12.blank_no_critical_three_mod_eight

end BB6.Agent12
