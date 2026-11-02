import InfiniteResidue
namespace BB6.HaltingFunnel

/-- Complete finite inverse image of a special G-output. The recursive
    branch can occur exactly once; the two cases are exhaustive. -/
theorem G_to_sixteen_k_plus_twentyfour_three (t k c : Nat)
    (hg : G k c = (16*t+24,3)) :
    (k=4*t+5 ∧ c=8*t+15) ∨ (k=6*t+9 ∧ c=4*t+6) := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases hs : c<2*k
    · have hlt : k-(c/2+1)<k := by omega
      have hg' : G (k-(c/2+1)) (2*c+3) = (16*t+24,3) := by
        rw [G] at hg
        simpa only [hs,dite_true] using hg
      rcases ih _ hlt _ hg' with h | h
      · right
        omega
      · omega
    · by_cases hm : c≤2*k+1
      · rw [G] at hg
        simp only [hs,dite_false,hm,ite_eq_left] at hg
        have hx : 0=16*t+24 := (Prod.mk.inj hg).1
        omega
      · rw [G] at hg
        simp only [hs,dite_false,hm,ite_false] at hg
        have hxy:=Prod.mk.inj hg
        left
        omega

/-- Exact T-predecessor classification of the c=3 gateway. -/
theorem T_to_sixteen_k_twentyfour_three (t a c : Nat)
    (ht : T a c = some (16*t+24,3)) :
    (a=8*t+9 ∧ c=8*t+17) ∨ (a=12*t+17 ∧ c=4*t+8) := by
  by_cases h0 : c=0
  · subst c
    simp [T] at ht
  · by_cases h1 : c=1
    · subst c
      simp [T] at ht
    · by_cases ha : a%2=0
      · have hh : T a c = some (a+3,c-2) := by
          simp [T,h0,h1,ha]
        have hxy := Prod.mk.inj (Option.some.inj (hh.symm.trans ht))
        omega
      · by_cases h2 : c=2
        · subst c
          simp [T,h0,h1,ha] at ht
        · by_cases h3 : c=3
          · subst c
            have hg : G (a/2) 1 = (16*t+24,3) := by
              simpa [T,h0,h1,ha,h2] using ht
            rcases G_to_sixteen_k_plus_twentyfour_three t (a/2) 1 hg with h | h <;> omega
          · have hg : G (a/2+1) (c-2) = (16*t+24,3) := by
              simpa [T,h0,h1,ha,h2,h3] using ht
            rcases G_to_sixteen_k_plus_twentyfour_three t (a/2+1) (c-2) hg with h | h
            · left
              omega
            · right
              omega

/-- The entire residue class c=16*k+30 is unreachable from the true
    blank-entry hub (2,1), by modular obstruction in all inverse branches. -/
theorem blank_no_two_sixteen_k_thirty (t : Nat) :
    ¬BlankReach 2 (16*t+30) := by
  intro h
  cases h with
  | next a c _ _ hr ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c (16*t+30) (by omega) ht
      have ha' : a=16*t+29 := by omega
      subst a
      subst c
      cases hr with
      | next a c _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor a c (16*t+29) 0 ht2 (by omega) with h13 | h12
          · obtain ⟨hc1,hleft,hright⟩ := h13
            have ha' : a=16*t+27 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                rcases T_odd_left_predecessor x y (16*t+27) 1 ht3 (by omega) with hcase | hcase
                · omega
                · obtain ⟨heven,hge,hleft,hright⟩ := hcase
                  have hx : x=16*t+24 := by omega
                  have hy : y=3 := by omega
                  subst x
                  subst y
                  cases hr3 with
                  | next u v _ _ hr4 ht4 =>
                      rcases T_to_sixteen_k_twentyfour_three t u v ht4 with h | h
                      · obtain ⟨hu,hv⟩:=h
                        subst u
                        subst v
                        cases hr4 with
                        | next p q _ _ hr5 ht5 =>
                            rcases T_odd_left_predecessor p q (8*t+9) (8*t+17) ht5 (by omega) with h | h
                            · omega
                            · obtain ⟨heven,hge,hleft,hright⟩ := h
                              have hp : p=8*t+6 := by omega
                              have hq : q=8*t+19 := by omega
                              subst p
                              subst q
                              have hinv := blank_even_left_invariant (8*t+6) (8*t+19) hr5 (by omega) (by omega)
                              rcases hinv with h | h <;> omega
                      · obtain ⟨hu,hv⟩:=h
                        subst u
                        subst v
                        cases hr4 with
                        | next p q _ _ hr5 ht5 =>
                            rcases T_odd_left_predecessor p q (12*t+17) (4*t+8) ht5 (by omega) with h | h
                            · omega
                            · obtain ⟨heven,hge,hleft,hright⟩ := h
                              have hp : p=12*t+14 := by omega
                              have hq : q=4*t+10 := by omega
                              subst p
                              subst q
                              have hinv := blank_even_left_invariant (12*t+14) (4*t+10) hr5 (by omega) (by omega)
                              rcases hinv with h | h <;> omega
          · obtain ⟨heven,hge,hleft,hright⟩ := h12
            have ha' : a=16*t+26 := by omega
            have hc' : c=2 := by omega
            subst a
            subst c
            have hinv := blank_even_left_invariant (16*t+26) 2 hr2 (by omega) (by omega)
            rcases hinv with h | h <;> omega

/-- Every relevant power dominates its affine index. -/
theorem pow8k_large (k : Nat) : k+1 ≤ 2^(8*k) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hp : 2^(8*(k+1)) = 256*2^(8*k) := by
      have he : 8*(k+1) = 8*k+8 := by omega
      rw [he,Nat.pow_add]
      simp only [Nat.reducePow]
      omega
    rw [hp]
    omega

/-- All critical indices congruent to four modulo eight are excluded. -/
theorem blank_no_critical_eight_k_plus_four (k : Nat) :
    ¬BlankReach 2 (14*2^(8*k+4) - 2*(8*k+4) - 10) := by
  have hp : 2^(8*k+4) = 16*2^(8*k) := by
    rw [Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have hb : k+3 ≤ 14*2^(8*k) := by
    have hh:=pow8k_large k
    omega
  have hid : 14*2^(8*k+4) - 2*(8*k+4) - 10 =
      16*(14*2^(8*k)-k-3)+30 := by
    rw [hp]
    omega
  rw [hid]
  exact blank_no_two_sixteen_k_thirty _

theorem blank_no_critical_four_mod_eight (n : Nat) (hn : n%8=4) :
    ¬BlankReach 2 (14*2^n-2*n-10) := by
  have he : n=8*(n/8)+4 := by omega
  rw [he]
  exact blank_no_critical_eight_k_plus_four _

#print axioms BB6.HaltingFunnel.blank_no_critical_four_mod_eight

#print axioms BB6.HaltingFunnel.G_to_sixteen_k_plus_twentyfour_three
#print axioms BB6.HaltingFunnel.blank_no_two_sixteen_k_thirty
end BB6.HaltingFunnel
