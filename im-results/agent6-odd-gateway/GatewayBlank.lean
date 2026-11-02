import MassRestriction

namespace BB6Agent6

/-- Every odd-sector return with right counter 3 from a reachable
    blank-entry hub (even a, odd c >= 5) has left counter 4 mod 8.
    The exceptional synthetically possible hub (2,15) was excluded. -/
theorem blank_U_three_left_mod8 (n a c : Nat)
    (h : runT n (2,1) = some (a,c))
    (ha : a % 2 = 0) (hc : c % 2 = 1) (h5 : 5 ≤ c)
    (hthree : (U a c).2 = 3) :
    (U a c).1 % 8 = 4 := by
  have hr := blank_odd_section_restriction n (a,c) h hc ha
  rcases hr with htwo | hfour
  · have ha2 : a = 2 := htwo
    subst a
    have hcfifteen := (U_two_right_three_iff c hc).mp hthree
    subst c
    exact False.elim ((blank_ne_two_fifteen n) h)
  · exact U_four_multiple_right_three a c hfour hc h5 hthree

/-- The ensuing reset coordinate, after the c=3, c=1, c=0
    sequence, has residue 1 mod 8. -/
theorem blank_U_three_next_reset_mod8 (n a c : Nat)
    (h : runT n (2,1) = some (a,c))
    (ha : a % 2 = 0) (hc : c % 2 = 1) (h5 : 5 ≤ c)
    (hthree : (U a c).2 = 3) :
    ((U a c).1 + 5) % 8 = 1 := by
  have hh := blank_U_three_left_mod8 n a c h ha hc h5 hthree
  omega

#print axioms BB6Agent6.blank_U_three_left_mod8
#print axioms BB6Agent6.blank_U_three_next_reset_mod8
end BB6Agent6
