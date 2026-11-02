import P1Gate
import P1SixInverse
import P1SixArithmetic

namespace BB6.Agent50P1
open BB6.P1Reduction

/-- The even-parameter residual feeder is globally unreachable when three power obstructions hold. -/
theorem six_feeder_impossible (s:Nat) (he:s%2=0) (hs:8≤s)
    (hp9:∀j, 9*s+6≠14*2^j)
    (hp10:∀j, 10*s+8≠14*2^j)
    (hp15:∀j, 15*s+10≠14*2^j) :
    ¬BB6.Agent1.Reach (16*s+4) 3 := by
  intro h
  have hno : ∀ k, ¬GAncestor (16*s+4) 3 k 1 := by
    intro k hh
    rcases inverse_16s4_three (16*s+4) 3 k 1 s hh rfl rfl he (by omega) with
      h1 | h2 | h3 | h4 <;> omega
  obtain ⟨k,v,hanc,hv,hr⟩ := positive_G_feeder (16*s+4) 3
    (by omega) (by omega) (by decide) hno h
  rcases inverse_16s4_three (16*s+4) 3 k v s hanc rfl rfl he (by omega) with
    h1 | h2 | h3 | h4
  · obtain ⟨hk,hv'⟩ := h1
    have hx : 2*k-4=8*s-4 := by omega
    have hy : v+4=8*s+9 := by omega
    rw [hx,hy] at hr
    have hno1 : ∀ z, ¬GAncestor (8*s-4) (8*s+9) z 1 := by
      intro z hh
      rcases inverse_8sminus4 (8*s-4) (8*s+9) z 1 s hh rfl rfl he (by omega) with
        h1 | h2 <;> omega
    obtain ⟨z,w,hanc2,hw,hr2⟩ := positive_G_feeder (8*s-4) (8*s+9)
      (by omega) (by omega) (by omega) hno1 hr
    rcases inverse_8sminus4 (8*s-4) (8*s+9) z w s hanc2 rfl rfl he (by omega) with
      g1 | g2
    · obtain ⟨hz,hw'⟩ := g1
      have hx : 2*z-4=4*s-8 := by omega
      have hy : w+4=12*s+11 := by omega
      rw [hx,hy] at hr2
      have hno2 : ∀ q, ¬GAncestor (4*s-8) (12*s+11) q 1 := by
        intro q hh
        rcases inverse_4sminus8 (4*s-8) (12*s+11) q 1 s hh rfl rfl he
          (by omega) with h1 | h2 <;> omega
      obtain ⟨q,u,hanc3,hu,hr3⟩ := positive_G_feeder (4*s-8) (12*s+11)
        (by omega) (by omega) (by omega) hno2 hr2
      rcases inverse_4sminus8 (4*s-8) (12*s+11) q u s hanc3 rfl rfl he
        (by omega) with p1 | p2
      · obtain ⟨hq,hu'⟩ := p1
        have hx : 2*q-4=2*s-10 := by omega
        have hy : u+4=14*s+11 := by omega
        rw [hx,hy] at hr3
        have hm := BB6.Agent1.reachable_even_mod4 (2*s-10) (14*s+11) hr3
          (by omega) (by omega)
        rcases hm with hv | hv <;> omega
      · obtain ⟨hq,hu'⟩ := p2
        have hx : 2*q-4=9*s-6 := by omega
        have hy : u+4=7*s+6 := by omega
        rw [hx,hy] at hr3
        obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (9*s-6) (7*s+6)
          hr3 (by omega) (by omega) (by omega)
        exact hp9 j (by omega)
    · obtain ⟨hz,hw'⟩ := g2
      have hx : 2*z-4=10*s-4 := by omega
      have hy : w+4=6*s+6 := by omega
      rw [hx,hy] at hr2
      obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (10*s-4) (6*s+6)
        hr2 (by omega) (by omega) (by omega)
      exact hp10 j (by omega)
  · obtain ⟨hk,hv'⟩ := h2
    have hx : 2*k-4=12*s-2 := by omega
    have hy : v+4=4*s+5 := by omega
    rw [hx,hy] at hr
    have hm := BB6.Agent1.reachable_even_mod4 (12*s-2) (4*s+5) hr
      (by omega) (by omega)
    rcases hm with h | h <;> omega
  · obtain ⟨hk,hv'⟩ := h3
    have hx : 2*k-4=14*s-2 := by omega
    have hy : v+4=2*s+3 := by omega
    rw [hx,hy] at hr
    have hm := BB6.Agent1.reachable_even_mod4 (14*s-2) (2*s+3) hr
      (by omega) (by omega)
    rcases hm with h | h <;> omega
  · obtain ⟨hk,hv'⟩ := h4
    have hx : 2*k-4=15*s-2 := by omega
    have hy : v+4=s+2 := by omega
    rw [hx,hy] at hr
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (15*s-2) (s+2)
      hr (by omega) (by omega) (by omega)
    exact hp15 j (by omega)

/-- Second infinite unresolved P1 critical-index class eliminated, n≡6 (mod16). -/
theorem blank_no_critical_six_mod_sixteen (k:Nat) :
    ¬BB6.Agent1.Reach 2 (14*2^(16*k+6)-2*(16*k+6)-10) := by
  let d := 14*2^(16*k+6)-2*(16*k+6)-10
  have ht := six_target k
  have hs := s6_large k
  have he := s6_even k
  have hbig : 10≤d := by dsimp [d]; omega
  have hmod : d%4=2 := by
    have hd : d=16*s6 k+10 := by dsimp [d]; omega
    rw [hd]
    omega
  intro hr
  have hthree := critical_target_implies_three d hbig hmod hr
  have hshape : d-6=16*s6 k+4 := by dsimp [d]; omega
  rw [hshape] at hthree
  exact (six_feeder_impossible (s6 k) he (by omega)
    (six_no_power_9 k) (six_no_power_10 k) (six_no_power_15 k)) hthree

#print axioms six_feeder_impossible
#print axioms blank_no_critical_six_mod_sixteen
end BB6.Agent50P1
