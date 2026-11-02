import P1ResidualReach
namespace BB6.Agent50P1

/-- Inversion helper preserving equations between predecessor parameters. -/
theorem last_predecessor (b d : Nat) (hr : BB6.Agent1.Reach b d)
    (hne : b ≠ 2 ∨ d ≠ 1) :
    ∃ a c, BB6.Agent1.Reach a c ∧ BB6.Agent1.T a c = some (b,d) := by
  cases hr with
  | init => rcases hne with hh | hh <;> contradiction
  | next a c _ _ hr ht => exact ⟨a,c,hr,ht⟩

/-- Universal residual critical reset reduction within the Agent1 Reach predicate. -/
theorem critical_target_implies_three (d : Nat)
    (hd : 10 ≤ d) (hm : d%4=2) :
    BB6.Agent1.Reach 2 d → BB6.Agent1.Reach (d-6) 3 := by
  intro h
  obtain ⟨a,c,hr,ht⟩ := last_predecessor 2 d h (Or.inr (by omega))
  obtain ⟨hc0,hd'⟩ := BB6.Agent1.T_to_two_positive a c d ht (by omega)
  have ha : a=d-1 := by omega
  have hreach : BB6.Agent1.Reach (d-1) 0 := by
    simpa only [ha,hc0] using hr
  obtain ⟨x,y,hr2,ht2⟩ := last_predecessor (d-1) 0 hreach (Or.inr (by decide))
  have hodd : (d-1)%2=1 := by omega
  rcases BB6.Agent1.T_to_odd_zero x y (d-1) ht2 hodd with h1 | h2
  · obtain ⟨hy,hx⟩ := h1
    have hxa : x=d-3 := by omega
    have hreach2 : BB6.Agent1.Reach (d-3) 1 := by
      simpa only [hxa,hy] using hr2
    obtain ⟨z,w,hprev,heven,hz,hw⟩ :=
      BB6.Agent1.odd_parent_general (d-3) 1 hreach2
        (by omega) (by decide)
    have hz' : z=d-6 := by omega
    have hw' : w=3 := by omega
    simpa only [hz',hw'] using hprev
  · obtain ⟨heven,hy,hx⟩ := h2
    have hxa : x=d-4 := by omega
    have hreach2 : BB6.Agent1.Reach (d-4) 2 := by
      simpa only [hxa,hy] using hr2
    have inv := BB6.Agent1.reachable_even_mod4 (d-4) 2 hreach2
      (by decide) (by omega)
    rcases inv with h | h <;> omega

/-- Unreachable all-time critical halting hub for every n = 16k+10. -/
theorem blank_no_critical_10_mod16 (k : Nat) :
    ¬BB6.Agent1.Reach 2 (14*2^(16*k+10)-2*(16*k+10)-10) := by
  let d := 14*2^(16*k+10)-2*(16*k+10)-10
  have hb : 10≤d := by
    have h := s_ge_three k
    have hx := target_shape k
    dsimp [d]
    omega
  have hm : d%4=2 := by
    have hs := s_odd k
    have ht := target_shape k
    have he : d=16*s k+18 := by dsimp [d]; omega
    rw [he]
    omega
  intro hr
  have h := critical_target_implies_three d hb hm hr
  have ht := blank_no_residual_critical_10_mod16 k
  have he : d-6=14*2^(16*k+10)-2*(16*k+10)-16 := by dsimp [d]; omega
  exact ht (he ▸ h)

#print axioms critical_target_implies_three
#print axioms blank_no_critical_10_mod16
end BB6.Agent50P1
