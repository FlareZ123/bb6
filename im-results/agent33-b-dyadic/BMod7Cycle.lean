import BMod7Period
namespace BB6.OneDim

theorem scalarA_pow7_at_odd_index (a : Nat)
    (hodd : a%2=1) (hnot2 : a%3≠2) :
    (iterG a 0)%7=4 ∨ (iterG a 0)%7=5 := by
  have hv : a%6=1 ∨ a%6=3 := by omega
  have hp := five_pow_mod7_mod6 a
  have h := iterG_zero_mod7 a
  rcases hv with h1 | h3
  · rw [h1] at hp
    simp at hp
    left
    omega
  · rw [h3] at hp
    simp at hp
    right
    omega

#print axioms scalarA_pow7_at_odd_index
end BB6.OneDim
