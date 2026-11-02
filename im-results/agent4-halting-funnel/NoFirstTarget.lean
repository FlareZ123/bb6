import BlankInvariants
namespace BB6.HaltingFunnel

/-- Whenever G returns first coordinate zero, its other output is odd. -/
theorem G_zero_second_odd (k c : Nat) (h:(G k c).1=0) :
    (G k c).2%2=1 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c<2*k
    · rw [G] at h ⊢
      simp only [h1,dite_true] at h ⊢
      exact ih _ (by omega) _ h
    · by_cases h2 : c≤2*k+1
      · rw [G] at h ⊢
        simp only [h1,dite_false,h2,ite_eq_left] at h ⊢
        omega
      · rw [G] at h ⊢
        simp [h1,h2] at h

/-- All transitions with first output 1 are impossible. -/
theorem T_ne_left_one (a c d:Nat) : T a c ≠ some (1,d) := by
  intro ht
  by_cases h0 : c=0
  · subst c
    simp [T] at ht
  · by_cases h1 : c=1
    · subst c
      simp [T] at ht
    · by_cases ha : a%2=0
      · have he:=T_even a c ha (by omega)
        have hx : a+3=1 :=
          (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2 : c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3 : c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hx : (G (a/2) 1).1=1 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hm:=G_left_mod_four (a/2) 1
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hx : (G (a/2+1) (c-2)).1=1 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hm:=G_left_mod_four (a/2+1) (c-2)
            omega

/-- No transition produces the state (0,2). -/
theorem T_ne_zero_two (a c:Nat) : T a c ≠ some (0,2) := by
  intro ht
  by_cases h0 : c=0
  · subst c
    simp [T] at ht
  · by_cases h1 : c=1
    · subst c
      simp [T] at ht
    · by_cases ha : a%2=0
      · have he := T_even a c ha (by omega)
        have hx : a+3=0 :=
          (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2 : c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3 : c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hz : (G (a/2) 1).1=0 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hd : (G (a/2) 1).2=2 :=
              (congrArg Prod.snd (Option.some.inj (he.symm.trans ht)))
            have odd:=G_zero_second_odd (a/2) 1 hz
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hz : (G (a/2+1) (c-2)).1=0 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hd : (G (a/2+1) (c-2)).2=2 :=
              (congrArg Prod.snd (Option.some.inj (he.symm.trans ht)))
            have odd:=G_zero_second_odd (a/2+1) (c-2) hz
            omega

/-- Only the (3,0) hub can transition directly to (2,4). -/
theorem T_to_two_four (a c : Nat) (ht:T a c=some (2,4)) :
    a=3 ∧ c=0 := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
    omega
  · by_cases h1:c=1
    · subst c
      simp [T] at ht
    · by_cases ha:a%2=0
      · have he := T_even a c ha (by omega)
        have hx : a+3=2 :=
          (Prod.mk.inj (Option.some.inj (he.symm.trans ht))).1
        omega
      · by_cases h2:c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3:c=3
          · subst c
            have he : T a 3=some (G (a/2) 1) := by simp [T,ha]
            have hx : (G (a/2) 1).1=2 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hm:=G_left_mod_four (a/2) 1
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hx : (G (a/2+1) (c-2)).1=2 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hm:=G_left_mod_four (a/2+1) (c-2)
            omega

/-- The two possible immediate predecessors of (3,0). -/
theorem T_to_three_zero (a c:Nat) (ht:T a c=some (3,0)) :
    (a=1∧c=1) ∨ (a=0∧c=2) := by
  by_cases h0:c=0
  · subst c
    simp [T] at ht
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
            have hx : (G (a/2) 1).1=3 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hm:=G_left_mod_four (a/2) 1
            omega
          · have he : T a c=some (G (a/2+1) (c-2)) := by
              simp [T,h0,h1,ha,h2,h3]
            have hx : (G (a/2+1) (c-2)).1=3 :=
              (congrArg Prod.fst (Option.some.inj (he.symm.trans ht)))
            have hm:=G_left_mod_four (a/2+1) (c-2)
            omega

/-- The first target (2,4) in the full critical family is unreachable
    from the real blank-entry accelerated state (2,1). -/
theorem blank_ne_first_critical : ¬BlankReach 2 4 := by
  intro h
  cases h with
  | next a c _ _ hr ht =>
      obtain ⟨ha,hc⟩ := T_to_two_four a c ht
      subst a
      subst c
      cases hr with
      | next a c _ _ hpre hstep =>
          rcases T_to_three_zero a c hstep with ⟨ha,hc⟩ | ⟨ha,hc⟩
          · subst a
            subst c
            cases hpre with
            | next x y _ _ _ htprev => exact T_ne_left_one x y 1 htprev
          · subst a
            subst c
            cases hpre with
            | next x y _ _ _ htprev => exact T_ne_zero_two x y htprev

#print axioms BB6.HaltingFunnel.blank_ne_first_critical
end BB6.HaltingFunnel
