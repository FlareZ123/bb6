import NoFourthTarget

namespace BB6.Agent12

/-- Every positive even right-counter configuration in the blank orbit has
    a left counter in one of two exact exponential corridors, depending
    on the parity of the left counter. -/
theorem blank_even_right_corridors (a c:Nat) (hr:BlankReach a c) :
    0<c → c%2=0 →
    ((a%2=0 → ∃ n:Nat, a+12=14*2^n) ∧
     (a%2=1 → ∃ n:Nat, a+9=14*2^n)) := by
  induction hr with
  | init =>
      intro hc hceven
      omega
  | next a c b d _ ht ih =>
      intro hd hdmod
      constructor
      · intro hb
        rcases T_positive_even_invariant a c b d ht hd hb with hb2 | hb4
        · subst b
          exact ⟨0, by decide⟩
        · obtain ⟨hbform,hcform⟩ :=
            T_to_mult4_even a c b d ht hb4 hdmod hd
          have haodd:a%2=1 := by omega
          have hceven:c%2=0 := by omega
          have hcpos:0<c := by omega
          rcases (ih hcpos hceven).2 haodd with ⟨n,hn⟩
          refine ⟨n+1, ?_⟩
          rw [Nat.pow_succ]
          omega
      · intro hbodd
        rcases T_odd_left_predecessor a c b d ht hbodd with hfirst | hsecond
        · omega
        · obtain ⟨haeven,hcpos,hbform,hdform⟩ := hsecond
          have hceven:c%2=0 := by omega
          rcases (ih (by omega : 0<c) hceven).1 haeven with ⟨n,hn⟩
          exact ⟨n, by omega⟩

/-- Explicit stronger shape theorem for every reachable positive even-even hub. -/
theorem blank_even_even_shape (a c:Nat) (hr:BlankReach a c)
    (hc:0<c) (hceven:c%2=0) (haeven:a%2=0) :
    ∃ n:Nat, a+12=14*2^n :=
  (blank_even_right_corridors a c hr hc hceven).1 haeven

#print axioms BB6.Agent12.blank_even_even_shape
end BB6.Agent12
