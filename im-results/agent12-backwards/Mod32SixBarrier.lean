import Mod16SixBarrier

namespace BB6.Agent12

/-- Eliminate the impossible initial case of backward reachability. -/
theorem blank_predecessor (b d:Nat) (hr:BlankReach b d)
    (hneq:b≠2 ∨ d≠1) :
    ∃ a c, BlankReach a c ∧ T a c=some (b,d) := by
  cases hr with
  | init => omega
  | next a c _ _ hpre ht => exact ⟨a,c,hpre,ht⟩

/-- The gateway (8m,3) cannot be reached when m is 2 mod 4 and large. -/
theorem blank_no_eight_multiple_three_mod_four (m:Nat)
    (hm:6≤m) (hm4:m%4=2) : ¬BlankReach (8*m) 3 := by
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
                    have hinv:=blank_even_left_invariant s r hpre4 (by omega) hs
                    rcases hinv with h | h <;> omega
/-- Unreachable right-counter residue 22 mod 32 at a=2. -/
theorem blank_no_twentytwo_mod_thirtytwo (d:Nat)
    (hl:54≤d) (hmod:d%32=22) : ¬BlankReach 2 d := by
  let m := (d-6)/8
  have hm:6≤m := by dsimp [m]; omega
  have hd:d=8*m+6 := by dsimp [m]; omega
  have hm4:m%4=2 := by omega
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
                  have hblank:=blank_no_eight_multiple_three_mod_four m hm hm4
                  have h8m:u=8*m := by omega
                  have h3:v=3 := by omega
                  exact hblank (by simpa [h8m,h3] using hpre3)
          · obtain ⟨hx,hy,_,_⟩ := hh
            have hinv:=blank_even_left_invariant x y hpre2 (by omega) hx
            rcases hinv with h | h <;> omega

#print axioms BB6.Agent12.blank_no_twentytwo_mod_thirtytwo
/-- Infinite critical family with n divisible by 16, including n=16. -/
theorem blank_no_critical_zero_mod_sixteen (n:Nat)
    (hn:16≤n) (hmod:n%16=0) :
    ¬BlankReach 2 (14*2^n - 2*n - 10) := by
  have hbound : ∀ j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hb:=hbound n
  have hl : 54≤14*2^n - 2*n - 10 := by omega
  have hp : (2^n)%32=0 := by
    have h5:n=n-5+5 := by omega
    rw [h5,Nat.pow_add]
    simp
  have hr : (14*2^n - 2*n - 10)%32=22 := by omega
  exact blank_no_twentytwo_mod_thirtytwo _ hl hr

#print axioms BB6.Agent12.blank_no_critical_zero_mod_sixteen

end BB6.Agent12
