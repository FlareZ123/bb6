import InfiniteResidue3
namespace BB6.HaltingFunnel

/-- Global blank-tape invariant: a positive even right counter cannot coexist
    with a left counter at least 24 and divisible by eight. -/
theorem blank_no_big_eight_even (k d : Nat)
    (hdpos : 0<d) (hdeven : d%2=0) :
    ¬BlankReach (8*k+24) d := by
  intro h
  cases h with
  | next a c _ _ hr ht =>
      obtain ⟨he, hleft,hright⟩ :=
        T_to_even_positive a c (8*k+24) d (by omega) (by omega) hdeven hdpos ht
      have ha : a=4*k+9 := by omega
      have hc : c=4*k+d+14 := by omega
      subst a
      subst c
      cases hr with
      | next u v _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor u v (4*k+9) (4*k+d+14) ht2 (by omega) with h | h
          · omega
          · obtain ⟨hu, hv,hleft,hright⟩:=h
            have hu' : u=4*k+6 := by omega
            have hv' : v=4*k+d+16 := by omega
            subst u
            subst v
            have hinv := blank_even_left_invariant (4*k+6) (4*k+d+16) hr2 (by omega) (by omega)
            rcases hinv with h | h <;> omega

#print axioms BB6.HaltingFunnel.blank_no_big_eight_even
end BB6.HaltingFunnel
