import ResetGate
namespace BB6.Agent1

/-- The first even-right counter at left eight is excluded by the exact
    exponential normal form for positive even-right hubs. -/
theorem blank_no_eight_positive_even (d:Nat) (hd:0<d) (he:d%2=0) :
    ¬Reach 8 d := by
  intro hr
  obtain ⟨j,hj⟩:=even_left_power_shape 8 d hr (by decide) hd he
  omega

/-- A short backwards decomposition forbids the exceptional hub (2,12).
    This is the only even-positive hub that could feed an 8-multiple zero. -/
theorem blank_no_two_twelve : ¬Reach 2 12 := by
  intro hr
  cases hr with
  | next a c _ _ hr ht =>
      obtain ⟨hc,hd⟩:=T_to_two_positive a c 12 ht (by omega)
      have ha : a=11 := by omega
      subst a
      subst c
      cases hr with
      | next b d _ _ hr2 ht2 =>
          rcases T_to_odd_zero b d 11 ht2 (by decide) with h1 | h2
          · obtain ⟨hd,hb⟩ := h1
            have hbeq:b=9 := by omega
            subst b
            subst d
            obtain ⟨z,w,hr3,hze,hz,hw⟩:=odd_parent_general 9 1 hr2 (by decide) (by decide)
            have hinv:=reachable_even_mod4 z w hr3 (by omega) hze
            rcases hinv with h | h <;> omega
          · obtain ⟨hb,hd,hbval⟩ := h2
            have hbeq:b=8 := by omega
            subst b
            subst d
            exact blank_no_eight_positive_even 2 (by decide) (by decide) hr2

/-- An even-zero-output G call is necessarily a direct high branch. -/
theorem G_to_zero (k c b:Nat) (h:G k c=(b,0)) :
    b=4*k+4 ∧ c=2*k+2 := by
  obtain ⟨hb,hbound,hd⟩ := G_even_output k c b 0 h (by decide)
  constructor
  · exact hb
  · omega

/-- Every reachable zero-right hub has left counter not divisible by eight. -/
theorem blank_no_zero_mod_eight (b:Nat) (hr:Reach b 0) : b%8 ≠ 0 := by
  intro hb8
  cases hr with
  | next a c _ _ hr ht =>
      unfold T at ht
      by_cases hz:c=0
      · simp [hz] at ht
      · by_cases ho:c=1
        · simp [hz,ho] at ht
          have haodd : a%2=0 := by omega
          have hr1 : Reach a 1 := by simpa [ho] using hr
          have hinv:=reachable_even_mod4 a 1 hr1 (by decide) haodd
          rcases hinv with h | h <;> omega
        · by_cases he:a%2=0
          · simp [hz,ho,he] at ht
            omega
          · by_cases hc2:c=2
            · simp [hz,ho,he,hc2] at ht
            · by_cases hc3:c=3
              · simp [hz,ho,he,hc2,hc3] at ht
                have ho := G_second_odd (a/2) 1 (by decide)
                have hh : (G (a/2) 1).2 = 0 := congrArg Prod.snd ht
                rw [hh] at ho
                omega
              · simp [hz,ho,he,hc2,hc3] at ht
                obtain ⟨hb,hc⟩:=G_to_zero (a/2+1) (c-2) b ht
                have hab : a=2*(a/2)+1 := by omega
                have ha5 : a=5 := by
                  have hodd : a%2=1 := by omega
                  have hapos : 0<c := by omega
                  obtain ⟨x,y,hprev,hxe,hx,hy⟩ := odd_parent_general a c hr hodd hapos
                  have hinv:=reachable_even_mod4 x y hprev (by omega) hxe
                  rcases hinv with h | h <;> omega
                have hc10 : c=10 := by omega
                subst a
                subst c
                obtain ⟨x,y,hprev,hxe,hx,hy⟩ := odd_parent_general 5 10 hr (by decide) (by decide)
                have hx2:x=2 := by omega
                have hy12:y=12 := by omega
                subst x
                subst y
                exact False.elim (blank_no_two_twelve hprev)

#print axioms BB6.Agent1.blank_no_two_twelve
#print axioms BB6.Agent1.blank_no_zero_mod_eight
end BB6.Agent1
