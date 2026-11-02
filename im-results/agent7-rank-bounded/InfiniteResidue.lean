import NoSecondTarget

namespace BB6.HaltingFunnel

/-- Every predecessor of an even-positive counter with left coordinate
    `8*k+24` is forced into one precise affine pattern. -/
theorem T_to_eightk_twentyfour_two (k a c : Nat)
    (ht : T a c = some (8*k+24,2)) :
    a=4*k+9 ∧ c=4*k+16 := by
  by_cases h0 : c=0
  · subst c
    simp [T] at ht
  · by_cases h1 : c=1
    · subst c
      simp [T] at ht
    · by_cases ha : a%2=0
      · have hh : T a c = some (a+3,c-2) := by
          simp [T,h0,h1,ha]
        have heq := Prod.mk.inj (Option.some.inj (hh.symm.trans ht))
        omega
      · by_cases h2 : c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3 : c=3
          · subst c
            have hg : G (a/2) 1 = (8*k+24,2) := by
              simpa [T,h0,h1,ha,h2] using ht
            have hp := G_odd (a/2) 1 (by decide)
            have htwo : (G (a/2) 1).2=2 := congrArg Prod.snd hg
            omega
          · have hg : G (a/2+1) (c-2) = (8*k+24,2) := by
              simpa [T,h0,h1,ha,h2,h3] using ht
            obtain ⟨hb,hleft,hright⟩ :=
              G_even_positive_output_direct (a/2+1) (c-2) (8*k+24) 2 hg (by decide)
            omega

/-- Every (2, 8*k+28) is unreachable from the actual blank-entry hub,
    regardless of the number of accelerated transitions. -/
theorem blank_no_two_eightk_twenty_eight (k : Nat) :
    ¬BlankReach 2 (8*k+28) := by
  intro h
  cases h with
  | next a c _ _ hr ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c (8*k+28) (by omega) ht
      have ha' : a=8*k+27 := by omega
      subst a
      subst c
      cases hr with
      | next a c _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor a c (8*k+27) 0 ht2 (by omega) with h13 | h12
          · obtain ⟨hc1,hleft,hright⟩ := h13
            have ha' : a=8*k+25 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                rcases T_odd_left_predecessor x y (8*k+25) 1 ht3 (by omega) with hcase | hcase
                · omega
                · obtain ⟨heven,hge,hleft,hright⟩ := hcase
                  have hx : x=8*k+22 := by omega
                  have hy : y=3 := by omega
                  subst x
                  subst y
                  have hinv := blank_even_left_invariant (8*k+22) 3 hr3 (by omega) (by omega)
                  rcases hinv with h | h <;> omega
          · obtain ⟨heven,hge,hleft,hright⟩ := h12
            have ha' : a=8*k+24 := by omega
            have hc' : c=2 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                obtain ⟨hx,hy⟩ := T_to_eightk_twentyfour_two k x y ht3
                subst x
                subst y
                cases hr3 with
                | next u v _ _ hr4 ht4 =>
                    rcases T_odd_left_predecessor u v (4*k+9) (4*k+16) ht4 (by omega) with hcase | hcase
                    · omega
                    · obtain ⟨heven,hge,hleft,hright⟩ := hcase
                      have hu : u=4*k+6 := by omega
                      have hv : v=4*k+18 := by omega
                      subst u
                      subst v
                      have hinv := blank_even_left_invariant (4*k+6) (4*k+18) hr4 (by omega) (by omega)
                      rcases hinv with h | h <;> omega


#print axioms BB6.HaltingFunnel.blank_no_two_eightk_twenty_eight
#print axioms BB6.HaltingFunnel.T_to_eightk_twentyfour_two
end BB6.HaltingFunnel
