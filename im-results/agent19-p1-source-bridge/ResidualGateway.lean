import NoSecondTarget

namespace BB6.Agent19.P1

open BB6.HaltingFunnel

/-- Every reachable state other than the initial hub has a finite incoming edge.
    This helper avoids dependent elimination on arithmetic counter expressions. -/
theorem last_predecessor (b d : Nat) (hr : BlankReach b d)
    (hne : b ≠ 2 ∨ d ≠ 1) :
    ∃ a c, BlankReach a c ∧ T a c = some (b,d) := by
  cases hr with
  | init => rcases hne with hh | hh <;> contradiction
  | next a c _ _ hr ht => exact ⟨a,c,hr,ht⟩

/-- Uniform remaining-mod4 gateway: a large even right counter 2 mod 4
    can occur as a reachable two-left reset iff the unique corresponding
    odd-sector hub occurs. Generalizes Agent 4's d=42 equivalence. -/
theorem residual_gateway (d : Nat) (hd:10≤d) (hmod:d%4=2) :
    BlankReach 2 d ↔ BlankReach (d-6) 3 := by
  constructor
  · intro h
    obtain ⟨a,c,hpre,ht⟩ := last_predecessor 2 d h (Or.inr (by omega))
    obtain ⟨ha,hc⟩ := T_to_two_positive a c d (by omega) ht
    have ha' : a=d-1 := by omega
    have hpre' : BlankReach (d-1) 0 := by simpa [ha',hc] using hpre
    obtain ⟨x,y,hr,hxy⟩ := last_predecessor (d-1) 0 hpre' (Or.inr (by decide))
    have haodd : (d-1)%2=1 := by omega
    rcases T_odd_left_predecessor x y (d-1) 0 hxy haodd with
        ⟨hy,hb,hd0⟩ | ⟨hxe,hbound,hb,hd0⟩
    · have hx : x=d-3 := by omega
      have hy' : y=1 := by omega
      have hr' : BlankReach (d-3) 1 := by simpa [hx,hy'] using hr
      obtain ⟨u,v,hprev,huv⟩ := last_predecessor (d-3) 1 hr' (Or.inl (by omega))
      have htargetodd : (d-3)%2=1 := by omega
      rcases T_odd_left_predecessor u v (d-3) 1 huv htargetodd with
          ⟨hv,hb,hd1⟩ | ⟨hue,hbound,hb,hd1⟩
      · omega
      · have hu : u=d-6 := by omega
        have hv : v=3 := by omega
        simpa [hu,hv] using hprev
    · have hx : x=d-4 := by omega
      have hy' : y=2 := by omega
      have hr' : BlankReach (d-4) 2 := by simpa [hx,hy'] using hr
      have heven : (d-4)%2=0 := by omega
      have hinv := blank_even_left_invariant (d-4) 2 hr' (by decide) heven
      rcases hinv with hh | hh <;> omega
  · intro h
    have ht1 : T (d-6) 3 = some (d-3,1) := by
      have h0 := T_even (d-6) 3 (by omega) (by omega)
      simpa only [show d-6+3=d-3 by omega, show 3-2=1 by decide] using h0
    have ht2 : T (d-3) 1 = some (d-1,0) := by
      have h0 : T (d-3) 1 = some (d-3+2,0) := by simp [T]
      simpa only [show d-3+2=d-1 by omega] using h0
    have ht3 : T (d-1) 0 = some (2,d) := by
      have h0 : T (d-1) 0 = some (2,d-1+1) := by simp [T]
      simpa only [show d-1+1=d by omega] using h0
    exact BlankReach.next (d-1) 0 2 d
      (BlankReach.next (d-3) 1 (d-1) 0
        (BlankReach.next (d-6) 3 (d-3) 1 h ht1) ht2) ht3

#print axioms BB6.Agent19.P1.residual_gateway

end BB6.Agent19.P1
