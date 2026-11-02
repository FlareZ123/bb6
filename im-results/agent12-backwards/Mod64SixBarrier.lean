import Mod32SixBarrier

namespace BB6.Agent12

/-- Third direct-branch layer excludes every (8m,3) with m>=16,m=0 mod8. -/
theorem blank_no_eight_multiple_three_mod_eight (m:Nat)
    (hm:16≤m) (hm8:m%8=0) : ¬BlankReach (8*m) 3 := by
  intro hr
  obtain ⟨a,c,hpre,ht⟩ := blank_predecessor (8*m) 3 hr (by omega)
  rcases T_to_eight_multiple_three m a c (by omega) ht with
    ⟨ha,hc⟩ | ⟨ha,hc⟩
  · have haodd:a%2=1 := by omega
    cases hpre with
    | init => omega
    | next p q _ _ hpre2 ht2 =>
        rcases T_odd_left_predecessor p q a c ht2 haodd with hh | hh
        · omega
        · obtain ⟨hp,hq,_,_⟩ := hh
          have hinv:=blank_even_left_invariant p q hpre2 (by omega) hp
          rcases hinv with h | h <;> omega
  · have haodd:a%2=1 := by omega
    cases hpre with
    | init => omega
    | next p q _ _ hpre2 ht2 =>
        rcases T_odd_left_predecessor p q a c ht2 haodd with hh | hh
        · omega
        · obtain ⟨hp,hq,_,_⟩ := hh
          have hpmod:p%4=0 := by omega
          have hqeven:q%2=0 := by omega
          have hqpos:0<q := by omega
          cases hpre2 with
          | init => omega
          | next z t _ _ hpre3 ht3 =>
              obtain ⟨hz,ht⟩:=T_to_mult4_even z t p q ht3 hpmod hqeven hqpos
              have hzodd:z%2=1 := by omega
              cases hpre3 with
              | init => omega
              | next s r _ _ hpre4 ht4 =>
                  rcases T_odd_left_predecessor s r z t ht4 hzodd with hh | hh
                  · omega
                  · obtain ⟨hs,hr,_,_⟩ := hh
                    have hsmod:s%4=0 := by omega
                    have hreven:r%2=0 := by omega
                    have hrpos:0<r := by omega
                    cases hpre4 with
                    | init => omega
                    | next w e _ _ hpre5 ht5 =>
                        obtain ⟨hw,he⟩:=T_to_mult4_even w e s r ht5 hsmod hreven hrpos
                        have hwodd:w%2=1 := by omega
                        cases hpre5 with
                        | init => omega
                        | next v f _ _ hpre6 ht6 =>
                            rcases T_odd_left_predecessor v f w e ht6 hwodd with hh | hh
                            · omega
                            · obtain ⟨hv,hf,_,_⟩ := hh
                              have hinv:=blank_even_left_invariant v f hpre6 (by omega) hv
                              rcases hinv with h | h <;> omega

/-- Unreachable right-counter residue 6 mod 64 for sufficiently large targets. -/
theorem blank_no_six_mod_sixtyfour (d:Nat)
    (hl:134≤d) (hmod:d%64=6) : ¬BlankReach 2 d := by
  let m := (d-6)/8
  have hm:16≤m := by dsimp [m]; omega
  have hd:d=8*m+6 := by dsimp [m]; omega
  have hm8:m%8=0 := by omega
  intro hr
  cases hr with
  | init => omega
  | next a c _ _ hpre ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c d (by omega) ht
      have haodd:a%2=1 := by omega
      cases hpre with
      | init => omega
      | next x y _ _ hpre2 ht2 =>
          rcases T_odd_left_predecessor x y a c ht2 haodd with hh | hh
          · obtain ⟨hy,hb,hd'⟩ := hh
            have hxodd:x%2=1 := by omega
            cases hpre2 with
            | init => omega
            | next u v _ _ hpre3 ht3 =>
                rcases T_odd_left_predecessor u v x y ht3 hxodd with hh | hh
                · omega
                · obtain ⟨hu,hv,_,_⟩ := hh
                  have hblank:=blank_no_eight_multiple_three_mod_eight m hm hm8
                  have h8m:u=8*m := by omega
                  have h3:v=3 := by omega
                  exact hblank (by simpa [h8m,h3] using hpre3)
          · obtain ⟨hx,hy,_,_⟩ := hh
            have hinv:=blank_even_left_invariant x y hpre2 (by omega) hx
            rcases hinv with h | h <;> omega

#print axioms BB6.Agent12.blank_no_six_mod_sixtyfour
/-- Infinite critical subfamily n>=24 with n%32=24. -/
theorem blank_no_critical_twentyfour_mod_thirtytwo (n:Nat)
    (hn:24≤n) (hmod:n%32=24) :
    ¬BlankReach 2 (14*2^n - 2*n - 10) := by
  have hbound : ∀ j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hb:=hbound n
  have hl : 134≤14*2^n - 2*n - 10 := by omega
  have hp : (2^n)%64=0 := by
    have h6:n=n-6+6 := by omega
    rw [h6,Nat.pow_add]
    simp
  have hr : (14*2^n - 2*n - 10)%64=6 := by omega
  exact blank_no_six_mod_sixtyfour _ hl hr

#print axioms BB6.Agent12.blank_no_critical_twentyfour_mod_thirtytwo

end BB6.Agent12
