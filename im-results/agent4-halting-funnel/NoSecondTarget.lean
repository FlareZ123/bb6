import NoFirstTarget
namespace BB6.HaltingFunnel

/-- No transition can output zero on the left and even c on the right. -/
theorem T_no_zero_even (a c d:Nat) (hd:d%2=0) : T a c ≠ some (0,d) := by
  intro ht
  by_cases h0:c=0
  · subst c
    simp [T] at ht
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
    · by_cases ha:a%2=0
      · have he:=T_even a c ha (by omega)
        have hx : a+3=0 := (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hxy:=Prod.mk.inj (Option.some.inj (he.symm.trans ht))
            have hh:=G_zero_second_odd (a/2) 1 hxy.1
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hxy:=Prod.mk.inj (Option.some.inj (he.symm.trans ht))
            have hh:=G_zero_second_odd (a/2+1) (c-2) hxy.1
            omega

/-- If G has positive even output second counter, its last branch was
    the immediate high branch: G recursion or middle branch always exit odd. -/
theorem G_even_positive_output_direct (k c b d : Nat)
    (ht:G k c=(b,d)) (hd:d%2=0) : 2*k+2≤c ∧ b=4*k+4 ∧ d=c-(2*k+2) := by
  by_cases h1:c<2*k
  · rw [G] at ht
    simp only [h1,dite_true] at ht
    have hcodd : (2*c+3)%2=1 := by omega
    have hh:=G_odd (k-(c/2+1)) (2*c+3) hcodd
    have hlast : d=(G (k-(c/2+1)) (2*c+3)).2 := congrArg Prod.snd ht.symm
    omega
  · by_cases h2:c≤2*k+1
    · rw [G] at ht
      simp only [h1,dite_false,h2,ite_eq_left] at ht
      have hh: d=2*c+3 := (congrArg Prod.snd ht).symm
      omega
    · have hbound : 2*k+2≤c := by omega
      have he:=G_big k c hbound
      rw [he] at ht
      have hxy:=Prod.mk.inj ht
      exact ⟨hbound,hxy.1.symm,hxy.2.symm⟩

/-- Every odd-first-coordinate successor comes either from c=1
    or from the even-first-coordinate two-cell reduction. -/
theorem T_odd_left_predecessor (a c b d:Nat) (ht:T a c=some (b,d))
    (hb:b%2=1) :
    (c=1 ∧ b=a+2 ∧ d=0) ∨
    (a%2=0 ∧ 2≤c ∧ b=a+3 ∧ d=c-2) := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
    omega
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
      left
      omega
    · by_cases ha:a%2=0
      · have he:=T_even a c ha (by omega)
        have hxy:=Prod.mk.inj (Option.some.inj (he.symm.trans ht))
        right
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hfst : b=(G (a/2) 1).1 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht))).symm
            have hm:=G_left_mod_four (a/2) 1
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hfst : b=(G (a/2+1) (c-2)).1 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht))).symm
            have hm:=G_left_mod_four (a/2+1) (c-2)
            omega

/-- The only predecessor of (13,1) is (10,3). -/
theorem T_to_thirteen_one (a c:Nat) (ht:T a c=some (13,1)) :
    a=10 ∧ c=3 := by
  rcases T_odd_left_predecessor a c 13 1 ht (by decide) with h | h
  · omega
  · omega

/-- The only predecessor of (3,10) is (0,12). -/
theorem T_to_three_ten (a c:Nat) (ht:T a c=some (3,10)) :
    a=0 ∧ c=12 := by
  rcases T_odd_left_predecessor a c 3 10 ht (by decide) with h | h
  · omega
  · omega

/-- The only predecessors of (15,0) are (13,1) and (12,2). -/
theorem T_to_fifteen_zero (a c:Nat) (ht:T a c=some (15,0)) :
    (a=13∧c=1) ∨ (a=12∧c=2) := by
  rcases T_odd_left_predecessor a c 15 0 ht (by decide) with h | h
  · left; omega
  · right; omega

/-- The only predecessor of (12,2) is (3,10). -/
theorem T_to_twelve_two (a c:Nat) (ht:T a c=some (12,2)) :
    a=3 ∧ c=10 := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
    · by_cases ha:a%2=0
      · have he:=T_even a c ha (by omega)
        have hx : a+3=12 :=
          (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hxy:=Option.some.inj (he.symm.trans ht)
            have hh:=G_odd (a/2) 1 (by decide)
            have hlast : (G (a/2) 1).2=2 := congrArg Prod.snd hxy
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hxy:=Option.some.inj (he.symm.trans ht)
            have hpar : (G (a/2+1) (c-2)).2%2=0 := by
              have hd : (G (a/2+1) (c-2)).2=2 := congrArg Prod.snd hxy
              omega
            have hdir:=G_even_positive_output_direct (a/2+1) (c-2) 12 2 hxy (by decide)
            rcases hdir with ⟨hbound,hleft,hright⟩
            have haodd : a%2=1 := by omega
            omega

/-- Every positive-c successor with left=2 must be created by c=0. -/
theorem T_to_two_positive (a c d:Nat) (hd:0<d)
    (ht:T a c=some (2,d)) : a+1=d ∧ c=0 := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
    omega
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
      omega
    · by_cases ha:a%2=0
      · have he:=T_even a c ha (by omega)
        have hf : a+3=2 := (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have he:T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hf : (G (a/2) 1).1=2 :=
              congrArg Prod.fst (Option.some.inj (he.symm.trans ht))
            have hm:=G_left_mod_four (a/2) 1
            omega
          · have he:T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hf : (G (a/2+1) (c-2)).1=2 :=
              congrArg Prod.fst (Option.some.inj (he.symm.trans ht))
            have hm:=G_left_mod_four (a/2+1) (c-2)
            omega

/-- The second critical target (2,16) is also unreachable from (2,1). -/
theorem blank_ne_second_critical : ¬BlankReach 2 16 := by
  intro h
  cases h with
  | next a c _ _ hpre ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c 16 (by decide) ht
      have ha15 : a=15 := by omega
      subst a
      subst c
      cases hpre with
      | next a c _ _ hpre2 ht2 =>
          rcases T_to_fifteen_zero a c ht2 with h13 | h12
          · obtain ⟨ha,hc⟩ := h13
            subst a
            subst c
            cases hpre2 with
            | next a c _ _ hpre3 ht3 =>
                obtain ⟨ha,hc⟩ := T_to_thirteen_one a c ht3
                subst a
                subst c
                have hinv:=blank_even_left_invariant 10 3 hpre3 (by decide) (by decide)
                rcases hinv with h | h <;> omega
          · obtain ⟨ha,hc⟩ := h12
            subst a
            subst c
            cases hpre2 with
            | next a c _ _ hpre3 ht3 =>
                obtain ⟨ha,hc⟩ := T_to_twelve_two a c ht3
                subst a
                subst c
                cases hpre3 with
                | next a c _ _ hpre4 ht4 =>
                    obtain ⟨ha,hc⟩ := T_to_three_ten a c ht4
                    subst a
                    subst c
                    cases hpre4 with
                    | next x y _ _ _ ht5 =>
                        exact T_no_zero_even x y 12 (by decide) ht5

#print axioms BB6.HaltingFunnel.blank_ne_second_critical
#print axioms BB6.HaltingFunnel.T_to_twelve_two
#print axioms BB6.HaltingFunnel.T_no_zero_even
end BB6.HaltingFunnel
