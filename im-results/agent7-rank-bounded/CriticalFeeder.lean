import OddCritical
namespace BB6.HaltingFunnel

/-- Positive-even reset target reachability is equivalent to the sole c=3
    feeder after the alternative even-sector branch is excluded. -/
theorem blank_two_iff_three_feeder (t : Nat)
    (hNoEven : ¬BlankReach (2*t+12) 2) :
    BlankReach 2 (2*t+16) ↔ BlankReach (2*t+10) 3 := by
  constructor
  · intro hr
    cases hr with
    | next a c _ _ hr1 ht =>
        obtain ⟨ha,hc⟩ := T_to_two_positive a c (2*t+16) (by omega) ht
        have ha' : a=2*t+15 := by omega
        subst a
        subst c
        cases hr1 with
        | next a c _ _ hr2 ht2 =>
            rcases T_odd_left_predecessor a c (2*t+15) 0 ht2 (by omega) with hcase | hcase
            · obtain ⟨hc1,hleft,hright⟩ := hcase
              have ha' : a=2*t+13 := by omega
              subst a
              subst c
              cases hr2 with
              | next x y _ _ hr3 ht3 =>
                  rcases T_odd_left_predecessor x y (2*t+13) 1 ht3 (by omega) with h | h
                  · omega
                  · obtain ⟨heven,hge,hleft,hright⟩ := h
                    have hx : x=2*t+10 := by omega
                    have hy : y=3 := by omega
                    subst x
                    subst y
                    exact hr3
            · obtain ⟨heven,hge,hleft,hright⟩ := hcase
              have ha' : a=2*t+12 := by omega
              have hc' : c=2 := by omega
              subst a
              subst c
              exact False.elim (hNoEven hr2)
  · intro hr
    have ht1 : T (2*t+10) 3 = some (2*t+13,1) := by
      simp [T]
    have hr1 : BlankReach (2*t+13) 1 :=
      BlankReach.next (2*t+10) 3 (2*t+13) 1 hr ht1
    have ht2 : T (2*t+13) 1 = some (2*t+15,0) := by
      simp [T]
    have hr2 : BlankReach (2*t+15) 0 :=
      BlankReach.next (2*t+13) 1 (2*t+15) 0 hr1 ht2
    have ht3 : T (2*t+15) 0 = some (2,2*t+16) := by
      simp [T]
    exact BlankReach.next (2*t+15) 0 2 (2*t+16) hr2 ht3

/-- Exact single c=3 gateway criterion for every critical index n>=1. -/
theorem blank_critical_iff_three_feeder (n : Nat) (hn : 1≤n) :
    BlankReach 2 (Gate n) ↔ BlankReach (Gate n-6) 3 := by
  have hp := power_ge_index n
  have hge : 16≤Gate n := by dsimp [Gate]; omega
  have heven : Gate n%2=0 := by dsimp [Gate]; omega
  let t := (Gate n-16)/2
  have he : Gate n=2*t+16 := by dsimp [t]; omega
  have hpre : Gate n-6=2*t+10 := by omega
  rw [hpre,he]
  apply blank_two_iff_three_feeder t
  have hno : ¬BlankReach (Gate n-4) 2 := blank_no_gate_even_feeder n hn
  have hfrom : Gate n-4=2*t+12 := by omega
  rw [hfrom] at hno
  exact hno

#print axioms BB6.HaltingFunnel.blank_two_iff_three_feeder
#print axioms BB6.HaltingFunnel.blank_critical_iff_three_feeder
end BB6.HaltingFunnel
