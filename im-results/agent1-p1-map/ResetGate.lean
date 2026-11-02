import PosEvenForm
namespace BB6.Agent1

theorem G_first_four (k c : Nat) : (G k c).1%4=0 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1:c<2*k
    · rw [G]
      simp only [h1,dite_true]
      exact ih _ (by omega) _
    · by_cases h2:c≤2*k+1
      · rw [G]
        simp [h1,h2]
      · rw [G]
        simp [h1,h2]

theorem reachable_even_mod4 (b d:Nat) (hr:Reach b d)
    (hd:0<d) (hb:b%2=0) : b=2 ∨ b%4=0 := by
  cases hr with
  | init => exact Or.inl rfl
  | next a c _ _ hpre ht =>
      unfold T at ht
      by_cases hz:c=0
      · simp [hz] at ht
        left
        omega
      · by_cases ho:c=1
        · simp [hz,ho] at ht
          omega
        · by_cases he:a%2=0
          · simp [hz,ho,he] at ht
            omega
          · by_cases hc2:c=2
            · simp [hz,ho,he,hc2] at ht
            · by_cases hc3:c=3
              · simp [hz,ho,he,hc2,hc3] at ht
                right
                have h := G_first_four (a/2) 1
                have heq : (G (a/2) 1).1=b := congrArg Prod.fst ht
                rw [heq] at h
                exact h
              · simp [hz,ho,he,hc2,hc3] at ht
                right
                have h := G_first_four (a/2+1) (c-2)
                have heq : (G (a/2+1) (c-2)).1=b := congrArg Prod.fst ht
                rw [heq] at h
                exact h

theorem T_to_two_positive (a c d:Nat)
    (h:T a c=some (2,d)) (hd:0<d) : c=0 ∧ d=a+1 := by
  unfold T at h
  by_cases hz:c=0
  · simp [hz] at h
    omega
  · by_cases ho:c=1
    · simp [hz,ho] at h
      omega
    · by_cases he:a%2=0
      · simp [hz,ho,he] at h
      · by_cases hc2:c=2
        · simp [hz,ho,he,hc2] at h
        · by_cases hc3:c=3
          · simp [hz,ho,he,hc2,hc3] at h
            have hx := G_first_four (a/2) 1
            have hb : (G (a/2) 1).1=2 := congrArg Prod.fst h
            rw [hb] at hx
            omega
          · simp [hz,ho,he,hc2,hc3] at h
            have hx := G_first_four (a/2+1) (c-2)
            have hb : (G (a/2+1) (c-2)).1=2 := congrArg Prod.fst h
            rw [hb] at hx
            omega

theorem T_to_odd_zero (a c b:Nat)
    (h:T a c=some (b,0)) (hb:b%2=1) :
    (c=1 ∧ b=a+2) ∨ (a%2=0 ∧ c=2 ∧ b=a+3) := by
  unfold T at h
  by_cases hz:c=0
  · simp [hz] at h
  · by_cases ho:c=1
    · simp [hz,ho] at h
      exact Or.inl (by omega)
    · by_cases he:a%2=0
      · simp [hz,ho,he] at h
        exact Or.inr (by omega)
      · by_cases hc2:c=2
        · simp [hz,ho,he,hc2] at h
        · by_cases hc3:c=3
          · simp [hz,ho,he,hc2,hc3] at h
            have hx := G_first_even (a/2) 1
            have hbeq : (G (a/2) 1).1=b := congrArg Prod.fst h
            rw [hbeq] at hx
            omega
          · simp [hz,ho,he,hc2,hc3] at h
            have hx := G_first_even (a/2+1) (c-2)
            have hbeq : (G (a/2+1) (c-2)).1=b := congrArg Prod.fst h
            rw [hbeq] at hx
            omega

theorem odd_parent_general (b d:Nat) (hr:Reach b d)
    (hb:b%2=1) (hd:0<d) :
    ∃ a c, Reach a c ∧ a%2=0 ∧ b=a+3 ∧ c=d+2 := by
  cases hr with
  | init => omega
  | next a c _ _ hr h =>
      unfold T at h
      by_cases hz:c=0
      · simp [hz] at h
        omega
      · by_cases ho:c=1
        · simp [hz,ho] at h
          omega
        · by_cases he:a%2=0
          · simp [hz,ho,he] at h
            exact ⟨a,c,hr,he,by omega,by omega⟩
          · by_cases hc2:c=2
            · simp [hz,ho,he,hc2] at h
            · by_cases hc3:c=3
              · simp [hz,ho,he,hc2,hc3] at h
                have heven := G_first_even (a/2) 1
                have hbeq : (G (a/2) 1).1=b := congrArg Prod.fst h
                rw [hbeq] at heven
                omega
              · simp [hz,ho,he,hc2,hc3] at h
                have heven := G_first_even (a/2+1) (c-2)
                have hbeq : (G (a/2+1) (c-2)).1=b := congrArg Prod.fst h
                rw [hbeq] at heven
                omega

/-- Uniform obstruction for every positive even counter divisible by four. -/
theorem reset_four_power (d:Nat) (hr:Reach 2 d)
    (hd:12≤d) (hfour:d%4=0) :
    ∃ j:Nat, d+8=14*2^j := by
  cases hr with
  | init => omega
  | next a c _ _ hr ht =>
      obtain ⟨hc0,hdval⟩ := T_to_two_positive a c d ht (by omega)
      subst c
      have haodd:a%2=1 := by omega
      cases hr with
      | next x y _ _ hr2 ht2 =>
          rcases T_to_odd_zero x y a ht2 haodd with h1 | h2
          · obtain ⟨hy,hax⟩:=h1
            subst y
            have hxodd:x%2=1 := by omega
            obtain ⟨z,w,hrz,hze,hxz,hw⟩ := odd_parent_general x 1 hr2 hxodd (by decide)
            have hinv := reachable_even_mod4 z w hrz (by omega) hze
            rcases hinv with h | h <;> omega
          · obtain ⟨hxe,hy,hax⟩:=h2
            subst y
            obtain ⟨j,hj⟩:=even_left_power_shape x 2 hr2 hxe (by decide) (by decide)
            exact ⟨j,by omega⟩

#print axioms BB6.Agent1.reset_four_power
end BB6.Agent1
