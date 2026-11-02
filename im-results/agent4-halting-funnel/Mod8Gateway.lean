import GModular

namespace BB6.HaltingFunnel

/-- Odd G input congruent to 1 mod 4 can only exit to c=3
    with left counter congruent 4 mod 8. -/
theorem G_one_mod_four_out_three (k c : Nat) (hc : c%4=1)
    (hthree : (G k c).2=3) : (G k c).1%8=4 := by
  rcases G_odd_modular k c hc with h | h
  · omega
  · exact h.1

/-- If G begins with even k and odd c, a c=3 output always has
    left coordinate congruent to 4 modulo 8, including recursive cases. -/
theorem G_even_k_odd_c_out_three (k c : Nat)
    (hk : k%2=0) (hc : c%2=1)
    (hthree : (G k c).2=3) : (G k c).1%8=4 := by
  by_cases h1 : c<2*k
  · have hrec : G k c = G (k-(c/2+1)) (2*c+3) := by
      rw [G]
      simp only [h1,dite_true]
    rw [hrec] at hthree ⊢
    apply G_one_mod_four_out_three _ _ (by omega) hthree
  · by_cases h2 : c≤2*k+1
    · have hbase : G k c = (0,2*c+3) := by
        rw [G]
        simp [h1,h2]
      rw [hbase] at hthree
      omega
    · have hbig : G k c = (4*k+4,c-(2*k+2)) := by
        rw [G]
        simp [h1,h2]
      rw [hbig]
      simp only [Prod.fst]
      omega

#print axioms BB6.HaltingFunnel.G_even_k_odd_c_out_three
end BB6.HaltingFunnel
