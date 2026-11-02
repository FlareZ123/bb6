import NoFourthTarget

namespace BB6.Agent12

/-- Complete G inverse for nonzero left output divisible by eight
    and right output exactly three. -/
theorem G_to_eight_multiple_three (m k c : Nat) (hm:0<m)
    (h:G k c=(8*m,3)) :
    (k=2*m-1 ∧ c=4*m+3) ∨ (k=3*m ∧ c=2*m) := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
      by_cases hlow:c<2*k
      · rw [G] at h
        simp only [hlow,dite_true] at h
        rcases ih _ (by omega) _ h with h1 | h2
        · right
          omega
        · omega
      · by_cases hmid:c≤2*k+1
        · rw [G] at h
          simp [hlow,hmid] at h
          omega
        · rw [G] at h
          simp [hlow,hmid] at h
          left
          omega

/-- Complete inverse of an exact T output (8m,3) for m>=1. -/
theorem T_to_eight_multiple_three (m a c:Nat) (hm:0<m)
    (ht:T a c=some (8*m,3)) :
    (a=4*m-3 ∧ c=4*m+5) ∨ (a=6*m-1 ∧ c=2*m+2) := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
    omega
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
    · by_cases ha:a%2=0
      · have he:=T_even a c ha (by omega)
        have hf : a+3=8*m :=
          (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have he:T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hg:G (a/2) 1=(8*m,3) := Option.some.inj (he.symm.trans ht)
            rcases G_to_eight_multiple_three m _ _ hm hg with hh | hh <;> omega
          · have he:T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hg:G (a/2+1) (c-2)=(8*m,3) :=
              Option.some.inj (he.symm.trans ht)
            rcases G_to_eight_multiple_three m _ _ hm hg with hh | hh
            · left
              omega
            · right
              omega

/-- Entire infinite mod16=14 class of reset targets is unreachable. -/
theorem blank_no_fourteen_mod_sixteen (d:Nat) (hlarge:30≤d)
    (hmod:d%16=14) : ¬BlankReach 2 d := by
  let m := (d-6)/8
  have hm3 : 3≤m := by dsimp [m]; omega
  have hd : d=8*m+6 := by dsimp [m]; omega
  have hmodm : m%2=1 := by omega
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
          · obtain ⟨hy,hb,hd'⟩ := hfirst
            have hxodd:x%2=1 := by omega
            cases hpre2 with
            | init => omega
            | next u v _ _ hpre3 ht3 =>
                rcases T_odd_left_predecessor u v x y ht3 hxodd with hh | hh
                · omega
                · obtain ⟨hu',hv',hb',hd''⟩ := hh
                  have hu:u=8*m := by omega
                  have hv:v=3 := by omega
                  cases hpre3 with
                  | init => omega
                  | next p q _ _ hpre4 ht4 =>
                      have ht4' : T p q=some (8*m,3) := by simpa [hu,hv] using ht4
                      rcases T_to_eight_multiple_three m p q (by omega) ht4' with
                        ⟨hp,hq⟩ | ⟨hp,hq⟩
                      · have hpodd:p%2=1 := by omega
                        cases hpre4 with
                        | init => omega
                        | next s t _ _ hpre5 ht5 =>
                            rcases T_odd_left_predecessor s t p q ht5 hpodd with hh | hh
                            · omega
                            · obtain ⟨hs,ht,_,_⟩ := hh
                              have hinv:=blank_even_left_invariant s t hpre5 (by omega) hs
                              rcases hinv with h | h <;> omega
                      · have hpodd:p%2=1 := by omega
                        cases hpre4 with
                        | init => omega
                        | next s t _ _ hpre5 ht5 =>
                            rcases T_odd_left_predecessor s t p q ht5 hpodd with hh | hh
                            · omega
                            · obtain ⟨hs,ht,_,_⟩ := hh
                              have hinv:=blank_even_left_invariant s t hpre5 (by omega) hs
                              rcases hinv with h | h <;> omega
          · obtain ⟨hx,hy,hb,hd'⟩ := hsecond
            have hbad:=blank_even_left_invariant x y hpre2 (by omega) hx
            rcases hbad with h | h <;> omega

#print axioms BB6.Agent12.blank_no_fourteen_mod_sixteen
/-- Infinite critical subfamily n ≡ 4 (mod 8), including the n=4 target 206. -/
theorem blank_no_critical_four_mod_eight (n:Nat) (hn:4≤n) (hnmod:n%8=4) :
    ¬BlankReach 2 (14*2^n - 2*n - 10) := by
  have hpowbound : ∀ j:Nat, j+1≤2^j := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ]
      omega
  have hsize:=hpowbound n
  have hlarge : 30≤14*2^n - 2*n - 10 := by omega
  have hpowmod : (2^n)%16=0 := by
    have h4:n=n-4+4 := by omega
    rw [h4, Nat.pow_add]
    simp
  have hmod : (14*2^n - 2*n - 10)%16=14 := by omega
  exact blank_no_fourteen_mod_sixteen _ hlarge hmod

#print axioms BB6.Agent12.blank_no_critical_four_mod_eight

end BB6.Agent12
