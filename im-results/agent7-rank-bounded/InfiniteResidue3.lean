import InfiniteResidue2
namespace BB6.HaltingFunnel

/-- Positive even-right output with left divisible four forces the direct
    high branch of G, with an exact affine predecessor formula. -/
theorem T_to_even_positive (a c b d : Nat)
    (hb : b%4=0) (hbig : 4≤b) (hd : d%2=0) (hdpos : 0<d)
    (ht : T a c = some (b,d)) :
    a%2=1 ∧ b=2*a+6 ∧ c=a+d+5 := by
  by_cases h0 : c=0
  · subst c
    simp [T] at ht
    omega
  · by_cases h1 : c=1
    · subst c
      simp [T] at ht
      omega
    · by_cases ha : a%2=0
      · have hh : T a c = some (a+3,c-2) := by
          simp [T,h0,h1,ha]
        have hxy := Prod.mk.inj (Option.some.inj (hh.symm.trans ht))
        omega
      · by_cases h2 : c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3 : c=3
          · subst c
            have hg : G (a/2) 1 = (b,d) := by
              simpa [T,h0,h1,ha,h2] using ht
            have hp := G_odd (a/2) 1 (by decide)
            have hright : (G (a/2) 1).2=d := congrArg Prod.snd hg
            omega
          · have hg : G (a/2+1) (c-2) = (b,d) := by
              simpa [T,h0,h1,ha,h2,h3] using ht
            obtain ⟨hbound,hleft,hright⟩ :=
              G_even_positive_output_direct (a/2+1) (c-2) b d hg hd
            omega

/-- The blank-entry orbit excludes a third infinite counter residue class. -/
theorem blank_no_two_sixteen_k_plus_sixtyfour (t : Nat) :
    ¬BlankReach 2 (16*t+64) := by
  intro h
  cases h with
  | next a c _ _ hr ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c (16*t+64) (by omega) ht
      have ha' : a=16*t+63 := by omega
      subst a
      subst c
      cases hr with
      | next a c _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor a c (16*t+63) 0 ht2 (by omega) with h13 | h12
          · obtain ⟨hc1,hleft,hright⟩ := h13
            have ha' : a=16*t+61 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                rcases T_odd_left_predecessor x y (16*t+61) 1 ht3 (by omega) with hcase | hcase
                · omega
                · obtain ⟨heven,hge,hleft,hright⟩ := hcase
                  have hx : x=16*t+58 := by omega
                  have hy : y=3 := by omega
                  subst x
                  subst y
                  have hinv := blank_even_left_invariant (16*t+58) 3 hr3 (by omega) (by omega)
                  rcases hinv with h | h <;> omega
          · obtain ⟨heven,hge,hleft,hright⟩ := h12
            have ha' : a=16*t+60 := by omega
            have hc' : c=2 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                obtain ⟨hx,hb,hd⟩ := T_to_even_positive x y (16*t+60) 2 (by omega) (by omega) (by decide) (by decide) ht3
                have hx' : x=8*t+27 := by omega
                have hy' : y=8*t+34 := by omega
                subst x
                subst y
                cases hr3 with
                | next u v _ _ hr4 ht4 =>
                    rcases T_odd_left_predecessor u v (8*t+27) (8*t+34) ht4 (by omega) with hcase | hcase
                    · omega
                    · obtain ⟨heven,hge,hleft,hright⟩:=hcase
                      have hu : u=8*t+24 := by omega
                      have hv : v=8*t+36 := by omega
                      subst u
                      subst v
                      cases hr4 with
                      | next p q _ _ hr5 ht5 =>
                          obtain ⟨hp,hb,hd⟩ := T_to_even_positive p q (8*t+24) (8*t+36) (by omega) (by omega) (by omega) (by omega) ht5
                          have hp' : p=4*t+9 := by omega
                          have hq' : q=12*t+50 := by omega
                          subst p
                          subst q
                          cases hr5 with
                          | next r s _ _ hr6 ht6 =>
                              rcases T_odd_left_predecessor r s (4*t+9) (12*t+50) ht6 (by omega) with hcase | hcase
                              · omega
                              · obtain ⟨heven,hge,hleft,hright⟩:=hcase
                                have hr : r=4*t+6 := by omega
                                have hs : s=12*t+52 := by omega
                                subst r
                                subst s
                                have hinv := blank_even_left_invariant (4*t+6) (12*t+52) hr6 (by omega) (by omega)
                                rcases hinv with h | h <;> omega

/-- All critical indices congruent to three modulo eight are excluded. -/
theorem blank_no_critical_eight_k_plus_three (k : Nat) :
    ¬BlankReach 2 (14*2^(8*k+3) - 2*(8*k+3) - 10) := by
  have hp : 2^(8*k+3) = 8*2^(8*k) := by
    rw [Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have hb : k+5 ≤ 7*2^(8*k) := by
    have hh := pow8k_large k
    omega
  have hid : 14*2^(8*k+3) - 2*(8*k+3) - 10 =
      16*(7*2^(8*k)-k-5)+64 := by
    rw [hp]
    omega
  rw [hid]
  exact blank_no_two_sixteen_k_plus_sixtyfour _

theorem blank_no_critical_three_mod_eight (n : Nat) (hn : n%8=3) :
    ¬BlankReach 2 (14*2^n-2*n-10) := by
  have he : n=8*(n/8)+3 := by omega
  rw [he]
  exact blank_no_critical_eight_k_plus_three _

#print axioms BB6.HaltingFunnel.blank_no_critical_three_mod_eight
#print axioms BB6.HaltingFunnel.T_to_even_positive
#print axioms BB6.HaltingFunnel.blank_no_two_sixteen_k_plus_sixtyfour
end BB6.HaltingFunnel
