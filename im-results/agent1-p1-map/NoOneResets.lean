import NoEightZero
namespace BB6.Agent1

/-- Except for the initial hub (2,1), no reset with right counter one
    modulo eight can ever occur. -/
theorem blank_no_two_one_mod_eight (j:Nat) (hj:0<j) : ¬Reach 2 (8*j+1) := by
  intro hr
  generalize heq : 8*j+1 = d at hr
  cases hr with
  | init => omega
  | next a c _ _ hpre ht =>
      obtain ⟨hc,hd⟩ := T_to_two_positive a c d ht (by omega)
      have hc0:c=0 := hc
      have ha8:a%8=0 := by omega
      subst c
      exact blank_no_zero_mod_eight a hpre ha8

#print axioms BB6.Agent1.blank_no_two_one_mod_eight
end BB6.Agent1
