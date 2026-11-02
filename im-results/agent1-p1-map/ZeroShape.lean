import NoEightZero
namespace BB6.Agent1

/-- Every reachable zero-right configuration with left divisible by four
    is either the first (4,0) or belongs to an explicit exponential family. -/
theorem zero_divfour_power (b:Nat) (hr:Reach b 0) (hb:b%4=0) :
    b=4 ∨ ∃j:Nat, b+12=28*2^j := by
  cases hr with
  | next a c _ _ hr ht =>
      unfold T at ht
      by_cases hz:c=0
      · simp [hz] at ht
      · by_cases ho:c=1
        · simp [hz,ho] at ht
          have haeven:a%2=0 := by omega
          have ha1:Reach a 1 := by simpa [ho] using hr
          have hinv:=reachable_even_mod4 a 1 ha1 (by decide) haeven
          rcases hinv with h | h
          · left; omega
          · omega
        · by_cases he:a%2=0
          · simp [hz,ho,he] at ht
            omega
          · by_cases hc2:c=2
            · simp [hz,ho,he,hc2] at ht
            · by_cases hc3:c=3
              · simp [hz,ho,he,hc2,hc3] at ht
                have ho:=G_second_odd (a/2) 1 (by decide)
                have hh:(G (a/2) 1).2=0 := congrArg Prod.snd ht
                rw [hh] at ho
                omega
              · simp [hz,ho,he,hc2,hc3] at ht
                obtain ⟨hbo,hco⟩:=G_to_zero (a/2+1) (c-2) b ht
                have hodd:a%2=1 := by omega
                obtain ⟨x,y,hprev,hxe,hx,hy⟩:=odd_parent_general a c hr hodd (by omega)
                have hypos:0<y := by omega
                have hyeven:y%2=0 := by omega
                obtain ⟨j,hj⟩:=even_left_power_shape x y hprev hxe hypos hyeven
                right
                refine ⟨j,?_⟩
                omega

/-- The j=0 member of the exponential zero-right family is unreachable. -/
theorem zero_divfour_power_strong (b:Nat) (hr:Reach b 0) (hb:b%4=0) :
    b=4 ∨ ∃j:Nat, b+12=28*2^(j+1) := by
  rcases zero_divfour_power b hr hb with h | ⟨j,hj⟩
  · exact Or.inl h
  · cases j with
    | zero =>
        have hb16:b=16 := by omega
        have bad:=blank_no_zero_mod_eight b hr
        omega
    | succ j =>
        exact Or.inr ⟨j,by simpa only [Nat.succ_eq_add_one] using hj⟩

#print axioms BB6.Agent1.zero_divfour_power_strong
end BB6.Agent1
