import EvenMiss
namespace BB6.Agent1
theorem reset_divfour_requires_even_two (s : Nat) (hr : Reach 2 s)
    (hs : 12≤s) (hmod : s%4=0) :
    ∃ b : Nat, Reach b 2 ∧ b+4=s := by
  cases hr with
  | init => omega
  | next a c _ _ hpre ht =>
    obtain ⟨hc,hd⟩:=T_to_two_positive a c s ht (by omega)
    have haodd : a%2=1 := by omega
    subst c
    cases hpre with
    | next x y _ _ hpre2 ht2 =>
      rcases T_to_odd_zero x y a ht2 haodd with h1 | h2
      · obtain ⟨hy,hx⟩:=h1
        subst y
        have hxodd:x%2=1:=by omega
        obtain ⟨z,w,hrz,hze,hxz,hw⟩:=
          odd_parent_general x 1 hpre2 hxodd (by decide)
        have hmod4 := reachable_even_mod4 z w hrz (by omega) hze
        rcases hmod4 with hz | hz <;> omega
      · obtain ⟨hxe,hy,hx⟩:=h2
        subst y
        exact ⟨x,hpre2,by omega⟩

theorem reset_divfour_odd_exponent (s : Nat) (hr : Reach 2 s)
    (hs : 12≤s) (hmod : s%4=0) :
    ∃ t : Nat, s+8=14*2^t ∧ t%2=1 := by
  obtain ⟨t,ht⟩ := reset_four_power s hr hs hmod
  obtain ⟨b,hrb,hsb⟩:=reset_divfour_requires_even_two s hr hs hmod
  obtain ⟨j,hj,hjodd⟩:=reachable_even_two_odd_exponent b hrb (by omega)
  have hpow : 2^t=2^j := by omega
  have htj : t=j := by
    by_cases h:t<j
    · have hp := Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) h
      omega
    · by_cases h':j<t
      · have hp := Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) h'
        omega
      · omega
  exact ⟨t,ht,by simpa [htj] using hjodd⟩

#print axioms BB6.Agent1.reset_divfour_requires_even_two
#print axioms BB6.Agent1.reset_divfour_odd_exponent
end BB6.Agent1
