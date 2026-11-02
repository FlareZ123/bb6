import Reachability

namespace BB6.HaltingFunnel

inductive ReachT : Nat → Nat → Nat → Nat → Prop where
  | refl (a c : Nat) : ReachT a c a c
  | next (a c b d e f : Nat) : T a c = some (b,d) → ReachT b d e f → ReachT a c e f

theorem reach_trans (a c b d e f : Nat) (h1 : ReachT a c b d)
    (h2 : ReachT b d e f) : ReachT a c e f := by
  induction h1 with
  | refl => exact h2
  | next a c b d x y ht ht2 ih => exact ReachT.next a c b d e f ht (ih h2)

/-- Any halting T trace beginning at even c either remains all-even, or
    it includes an odd-c hub with a strictly shorter halting suffix. -/
theorem even_trace_or_odd_tail (n a c : Nat) (h : HaltsIn n a c) :
    c%2=0 →
    EvenHIn n a c ∨
    ∃ m b d, m<n ∧ d%2=1 ∧ ReachT a c b d ∧ HaltsIn m b d := by
  induction h with
  | now a c ht =>
      intro hc
      exact .inl (EvenHIn.final a c hc ht)
  | next steps a c b d ht rest ih =>
      intro hc
      by_cases hd : d%2=0
      · rcases ih hd with hre | ⟨m,x,y,hlt,hodd,hreach,hhalting⟩
        · exact .inl (EvenHIn.cons steps a c b d hc ht hre)
        · exact .inr ⟨m,x,y,by omega,hodd,ReachT.next a c b d x y ht hreach,hhalting⟩
      · exact .inr ⟨steps,b,d,by omega,by omega,
          ReachT.next a c b d b d ht (ReachT.refl b d),rest⟩

/-- Every odd-c hub has a defined T successor. -/
theorem T_odd_defined (a c : Nat) (hc:c%2=1) : T a c ≠ none := by
  unfold T
  by_cases h0 : c=0
  · omega
  · by_cases h1 : c=1
    · simp [h0,h1]
    · by_cases ha : a%2=0
      · simp [h0,h1,ha]
      · have h2 : c≠2 := by omega
        by_cases h3 : c=3
        · simp [h0,h1,ha,h2,h3]
        · simp [h0,h1,ha,h2,h3]

/-- A formal sparse-target criterion for blank-tape halting under the
    independently restated accelerated map T, starting from (2,1). -/
theorem halting_implies_critical (n : Nat) :
    ∀ a c, HaltsIn n a c →
    (c%2=1 ∨ c=0 ∨ (a=2 ∧ c%2=0)) →
    ∃ m, ReachT a c 2 (C 0 m) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a c hh start
    rcases start with hodd | hzero | ⟨ha,hce⟩
    · cases hh with
      | now a c hnone => exact False.elim ((T_odd_defined a c hodd) hnone)
      | next k a c b d ht hrest =>
          have hlt : k<k+1 := by omega
          rcases T_odd_exit a c b d hodd ht with hod | ⟨he,hzero⟩
          · obtain ⟨m,hr⟩ := ih k hlt b d hrest (.inl hod)
            exact ⟨m,ReachT.next _ _ _ _ _ _ ht hr⟩
          · obtain ⟨m,hr⟩ := ih k hlt b d hrest (.inr (.inl hzero))
            exact ⟨m,ReachT.next _ _ _ _ _ _ ht hr⟩
    · subst c
      cases hh with
      | now a c hnone => simp [T] at hnone
      | next k a c b d ht hrest =>
          have hentry : b=2 ∧ d=a+1 := T_zero_entry a b d ht
          rcases hentry with ⟨hb,hd⟩
          subst b
          subst d
          have hlt : k<k+1 := by omega
          by_cases hp : (a+1)%2=1
          · obtain ⟨m,hr⟩ := ih k hlt 2 (a+1) hrest (.inl hp)
            exact ⟨m,ReachT.next _ _ _ _ _ _ ht hr⟩
          · obtain ⟨m,hr⟩ := ih k hlt 2 (a+1) hrest (.inr (.inr ⟨rfl,by omega⟩))
            exact ⟨m,ReachT.next _ _ _ _ _ _ ht hr⟩
    · subst a
      rcases even_trace_or_odd_tail n 2 c hh hce with heven | ⟨k,b,d,hlt,hod,hr,htail⟩
      · obtain ⟨m,hcritical⟩ := even_trace_from_two_iff n c heven
        exact ⟨m, by rw [hcritical]; exact ReachT.refl 2 (C 0 m)⟩
      · obtain ⟨m,hr2⟩ := ih k hlt b d htail (.inl hod)
        exact ⟨m, reach_trans 2 c b d 2 (C 0 m) hr hr2⟩

/-- Halting propagates backwards across any finite sequence of T transitions. -/
theorem reach_preserves_halting (a c b d : Nat) (hr : ReachT a c b d)
    (hh : ∃ s, HaltsIn s b d) : ∃ s, HaltsIn s a c := by
  induction hr with
  | refl => exact hh
  | next a c b d e f ht rest ih =>
      obtain ⟨s,hs⟩ := ih hh
      exact ⟨s+1, HaltsIn.next s a c b d ht hs⟩

/-- An exact logical equivalence: the blank-entry P1(2,1) halts iff
    its accelerated orbit reaches one of the sparse (2,C(0,n)) targets. -/
theorem blank_halts_iff_critical :
    (∃ s, HaltsIn s 2 1) ↔ (∃ n, ReachT 2 1 2 (C 0 n)) := by
  constructor
  · rintro ⟨s,hh⟩
    exact halting_implies_critical s 2 1 hh (.inl (by decide))
  · rintro ⟨n,hr⟩
    exact reach_preserves_halting 2 1 2 (C 0 n) hr ⟨2*n+2, halts_family_exact 0 n⟩

#print axioms BB6.HaltingFunnel.blank_halts_iff_critical
end BB6.HaltingFunnel
