import CSourceBridge16
set_option maxRecDepth 16384
namespace CCert

private theorem q_one_cases (u : Nat) :
    q (8*u+1) = q 1 ∨ q (8*u+1) = q 9 ∨ q (8*u+1) = q 17 := by
  by_cases hzero : u = 0
  · subst u
    left
    decide
  · by_cases heven : u % 2 = 0
    · right
      right
      exact q_congr_big _ _ (by omega) (by omega) (by omega)
    · right
      left
      exact q_congr_big _ _ (by omega) (by omega) (by omega)

private theorem q_two_cases (v : Nat) :
    q (16*v+2) = q 2 ∨ q (16*v+2) = q 18 := by
  by_cases hzero : v = 0
  · subst v
    left
    decide
  · right
    exact q_congr_big _ _ (by omega) (by omega) (by omega)

private theorem no_one_two_abstract (u v : Nat) :
    seen (q (8*u+1)) (q (16*v+2)) (q 0) = false := by
  rcases q_one_cases u with h1 | h9 | h17
  · rcases q_two_cases v with h2 | h18
    · rw [h1,h2]; decide
    · rw [h1,h18]; decide
  · rcases q_two_cases v with h2 | h18
    · rw [h9,h2]; decide
    · rw [h9,h18]; decide
  · rcases q_two_cases v with h2 | h18
    · rw [h17,h2]; decide
    · rw [h17,h18]; decide

private theorem not_reach_unseen (a k c : Nat)
    (h : seen (q a) (q k) (q c) = false) :
    ¬ BB6CLine.Reach (a,k,c) := by
  intro hr
  have hs := reachable_seen (source_reachable_embeds16 hr)
  rw [h] at hs
  cases hs

theorem published_no_one_two (u v : Nat) :
    ¬ BB6CLine.Reach (8*u+1,16*v+2,0) := by
  exact not_reach_unseen _ _ _ (no_one_two_abstract u v)

private theorem no_nine_fifteen_abstract (u v : Nat) :
    seen (q (16*u+9)) (q (16*v+15)) (q 0) = false := by
  have ha : q (16*u+9) = q 9 :=
    q_congr_big _ _ (by omega) (by omega) (by omega)
  have hk : q (16*v+15) = q 15 :=
    q_congr_big _ _ (by omega) (by omega) (by omega)
  rw [ha,hk]
  decide

theorem published_no_nine_fifteen (u v : Nat) :
    ¬ BB6CLine.Reach (16*u+9,16*v+15,0) := by
  exact not_reach_unseen _ _ _ (no_nine_fifteen_abstract u v)

private theorem no_one_seven_except_abstract (u v : Nat)
    (hpos : 0 < u ∨ 0 < v) :
    seen (q (16*u+1)) (q (16*v+7)) (q 0) = false := by
  rcases u with _ | u
  · rcases v with _ | v
    · omega
    · have hk : q (16*(v+1)+7) = q 23 :=
        q_congr_big _ _ (by omega) (by omega) (by omega)
      rw [hk]
      decide
  · have ha : q (16*(u+1)+1) = q 17 :=
      q_congr_big _ _ (by omega) (by omega) (by omega)
    rw [ha]
    rcases v with _ | v
    · decide
    · have hk : q (16*(v+1)+7) = q 23 :=
        q_congr_big _ _ (by omega) (by omega) (by omega)
      rw [hk]
      decide

theorem published_no_one_seven_except (u v : Nat)
    (hpos : 0 < u ∨ 0 < v) :
    ¬ BB6CLine.Reach (16*u+1,16*v+7,0) := by
  exact not_reach_unseen _ _ _ (no_one_seven_except_abstract u v hpos)

private theorem pow16 (m : Nat) (hm : 0 < m) : 16 ∣ 2^(2*m+2) := by
  obtain ⟨r,hr⟩ : ∃ r, 2*m+2 = 4+r := ⟨2*m-2, by omega⟩
  rw [hr, Nat.pow_add]
  change 16 ∣ 16*2^r
  exact ⟨2^r,rfl⟩

private theorem stop_eq16 (j m k : Nat) (hm : 0 < m)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%16=0 := by
  obtain ⟨z,hz⟩ := pow16 m hm
  have hprod : 16 ∣ 2^(2*m+2)*(j+3) := by
    refine ⟨z*(j+3), ?_⟩
    rw [hz]
    simp only [Nat.mul_assoc]
  rw [hk]
  exact Nat.mod_eq_zero_of_dvd hprod

theorem published_no_even_odd_halt_params
    (j m k : Nat) (hj : j%4=3) (hmj : (m+1)%16=j%16)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hm : 0 < m := by omega
  have hmod := stop_eq16 j m k hm hk
  have ha : 2*j+3=8*((2*j+3)/8)+1 := by omega
  have hb : k=16*(k/16)+2 := by omega
  rw [ha,hb]
  exact published_no_one_two _ _

theorem published_no_nine_fifteen_halt_params
    (j m k : Nat) (hj : j%8=3) (hmj : m%16=j%16)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hm : 0 < m := by omega
  have hmod := stop_eq16 j m k hm hk
  have ha : 2*j+3=16*((2*j+3)/16)+9 := by omega
  have hb : k=16*(k/16)+15 := by omega
  rw [ha,hb]
  exact published_no_nine_fifteen _ _

theorem published_no_one_seven_halt_params
    (j m k : Nat) (hj : j%8=7) (hmj : (m+8)%16=j%16)
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  have hm : 0 < m := by omega
  have hmod := stop_eq16 j m k hm hk
  have ha : 2*j+3=16*((j-7)/8+1)+1 := by omega
  have hb : k=16*(k/16)+7 := by omega
  rw [ha,hb]
  exact published_no_one_seven_except _ _ (Or.inl (by omega))

#print axioms published_no_one_two
#print axioms published_no_nine_fifteen
#print axioms published_no_one_seven_except
#print axioms published_no_even_odd_halt_params
#print axioms published_no_nine_fifteen_halt_params
#print axioms published_no_one_seven_halt_params
end CCert
