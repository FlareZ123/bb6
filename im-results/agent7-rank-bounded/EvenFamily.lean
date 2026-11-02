import InfiniteResidue5
namespace BB6.HaltingFunnel

/-- No blank-reachable accelerated hub has left counter one. -/
theorem blank_ne_one (d : Nat) : ¬BlankReach 1 d := by
  intro h
  cases h with
  | next a c _ _ hr ht => exact T_ne_left_one a c d ht

/-- No blank-reachable hub has left zero and even right counter. -/
theorem blank_ne_zero_even (d : Nat) (hd : d%2=0) : ¬BlankReach 0 d := by
  intro h
  cases h with
  | next a c _ _ hr ht => exact T_no_zero_even a c d hd ht

/-- No blank-reachable hub has left four and positive even right counter. -/
theorem blank_ne_four_even (d : Nat) (hd : 0<d) (he : d%2=0) :
    ¬BlankReach 4 d := by
  intro hr
  cases hr with
  | next a c _ _ hpre ht =>
    obtain ⟨ha,hb,hc⟩ := T_to_even_positive a c 4 d (by decide) (by decide) he hd ht
    omega

/-- No blank-reachable hub has left eight and positive even right counter. -/
theorem blank_ne_eight_even (d : Nat) (hd : 0<d) (he : d%2=0) :
    ¬BlankReach 8 d := by
  intro hr
  cases hr with
  | next a c _ _ hpre ht =>
    obtain ⟨ha,hb,hc⟩ := T_to_even_positive a c 8 d (by decide) (by decide) he hd ht
    have ha1 : a=1 := by omega
    subst a
    exact blank_ne_one c hpre

/-- Exhaustive left-counter classification for every actual blank-reachable
    hub with even positive right counter and even left counter. -/
theorem blank_even_hub_power (b : Nat) :
    ∀ d, BlankReach b d → 0<d → d%2=0 → b%2=0 →
      ∃ j : Nat, b+12 = 14*2^j := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro d hr hdpos hdeven heven
    by_cases hb2 : b=2
    · subst b
      exact ⟨0, by decide⟩
    · have hfour : b%4=0 := by
        have hx := blank_even_left_invariant b d hr hdpos heven
        rcases hx with h | h
        · exact False.elim (hb2 h)
        · exact h
      by_cases hbsmall : b<12
      · have cases : b=0 ∨ b=4 ∨ b=8 := by omega
        rcases cases with h | h | h
        · subst b
          exact False.elim (blank_ne_zero_even d hdeven hr)
        · subst b
          exact False.elim (blank_ne_four_even d hdpos hdeven hr)
        · subst b
          exact False.elim (blank_ne_eight_even d hdpos hdeven hr)
      · have hbig : 12≤b := by omega
        have hprev := blank_even_two_back b d hfour hbig hdpos hdeven hr
        have hlt : b/2-6 < b := by omega
        have hprevEven : (b/2-6)%2=0 := by omega
        have hprevDpos : 0<b/2+d+4 := by omega
        have hprevDeven : (b/2+d+4)%2=0 := by omega
        obtain ⟨j,hj⟩ := ih (b/2-6) hlt (b/2+d+4) hprev
          hprevDpos hprevDeven hprevEven
        refine ⟨j+1, ?_⟩
        have hbexpr : b+12 = 2*((b/2-6)+12) := by omega
        rw [hbexpr,hj,Nat.pow_succ]
        omega

#print axioms BB6.HaltingFunnel.blank_even_hub_power
end BB6.HaltingFunnel
