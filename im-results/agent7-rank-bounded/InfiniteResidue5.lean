import InfiniteResidue4
namespace BB6.HaltingFunnel

/-- Exact two-step inverse of the even-counter high branch on a genuinely
    blank-reachable state. This gives a reusable symbolic backward operation. -/
theorem blank_even_two_back (b d : Nat)
    (hb : b%4=0) (hbig : 12≤b) (hdpos : 0<d) (hdeven : d%2=0)
    (hr : BlankReach b d) :
    BlankReach (b/2-6) (b/2+d+4) := by
  cases hr with
  | init => omega
  | next a c _ _ hr ht =>
      obtain ⟨ha,hleft,hright⟩ :=
        T_to_even_positive a c b d hb (by omega) hdeven hdpos ht
      cases hr with
      | init => omega
      | next u v _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor u v a c ht2 (by omega) with hcase | hcase
          · omega
          · obtain ⟨hu,hv,hleft2,hright2⟩ := hcase
            have hu' : u=b/2-6 := by omega
            have hv' : v=b/2+d+4 := by omega
            simpa [hu',hv'] using hr2

/-- A fourth infinite positive-counter residue exclusion, based on
    two inverse even-sector macro stages followed by the global mod8 guard. -/
theorem blank_no_two_thirtytwo_k_plus_136 (t : Nat) :
    ¬BlankReach 2 (32*t+136) := by
  intro hr
  cases hr with
  | next a c _ _ hr ht =>
      obtain ⟨ha,hc⟩ := T_to_two_positive a c (32*t+136) (by omega) ht
      have ha' : a=32*t+135 := by omega
      subst a
      subst c
      cases hr with
      | next a c _ _ hr2 ht2 =>
          rcases T_odd_left_predecessor a c (32*t+135) 0 ht2 (by omega) with h1 | h2
          · obtain ⟨hc,hleft,hright⟩:=h1
            have ha':a=32*t+133 := by omega
            subst a
            subst c
            cases hr2 with
            | next x y _ _ hr3 ht3 =>
                rcases T_odd_left_predecessor x y (32*t+133) 1 ht3 (by omega) with h | h
                · omega
                · obtain ⟨heven,hge,hleft,hright⟩ := h
                  have hx : x=32*t+130 := by omega
                  have hy : y=3 := by omega
                  subst x
                  subst y
                  have hinv := blank_even_left_invariant (32*t+130) 3 hr3 (by omega) (by omega)
                  rcases hinv with h | h <;> omega
          · obtain ⟨heven,hge,hleft,hright⟩:=h2
            have ha' : a=32*t+132 := by omega
            have hc' : c=2 := by omega
            subst a
            subst c
            have hr1 : BlankReach (16*t+60) (16*t+72) := by
              have hv:=blank_even_two_back (32*t+132) 2 (by omega) (by omega)
                (by omega) (by omega) hr2
              have hleft : (32*t+132)/2-6 = 16*t+60 := by omega
              have hright : (32*t+132)/2+2+4 = 16*t+72 := by omega
              rw [hleft,hright] at hv
              exact hv
            have hr2' : BlankReach (8*t+24) (24*t+106) := by
              have hv:=blank_even_two_back (16*t+60) (16*t+72) (by omega)
                (by omega) (by omega) (by omega) hr1
              have hleft : (16*t+60)/2-6 = 8*t+24 := by omega
              have hright : (16*t+60)/2+(16*t+72)+4 = 24*t+106 := by omega
              rw [hleft,hright] at hv
              exact hv
            exact blank_no_big_eight_even t (24*t+106) (by omega) (by omega) hr2'

/-- All indices n congruent to seven modulo 16 are unreachable. -/
theorem blank_no_critical_sixteen_k_plus_seven (k : Nat) :
    ¬BlankReach 2 (14*2^(16*k+7) - 2*(16*k+7) - 10) := by
  have hp : 2^(16*k+7) = 128*2^(16*k) := by
    rw [Nat.pow_add]
    simp only [Nat.reducePow]
    omega
  have hb : k+5 ≤ 56*2^(16*k) := by
    have hh := pow8k_large (2*k)
    have hpow : 8*(2*k)=16*k := by omega
    rw [hpow] at hh
    omega
  have hid : 14*2^(16*k+7) - 2*(16*k+7) - 10 =
      32*(56*2^(16*k)-k-5)+136 := by
    rw [hp]
    omega
  rw [hid]
  exact blank_no_two_thirtytwo_k_plus_136 _

theorem blank_no_critical_seven_mod_sixteen (n : Nat) (hn : n%16=7) :
    ¬BlankReach 2 (14*2^n-2*n-10) := by
  have he : n=16*(n/16)+7 := by omega
  rw [he]
  exact blank_no_critical_sixteen_k_plus_seven _

#print axioms BB6.HaltingFunnel.blank_no_critical_seven_mod_sixteen
#print axioms BB6.HaltingFunnel.blank_even_two_back
#print axioms BB6.HaltingFunnel.blank_no_two_thirtytwo_k_plus_136
end BB6.HaltingFunnel
