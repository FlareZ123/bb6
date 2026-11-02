import HaltingFunnel

namespace BB6.HaltingFunnel

theorem C_even (j n : Nat) : C j n % 2 = 0 := by
  induction n generalizing j with
  | zero => simp [C]
  | succ n ih =>
    simp only [C]
    have h1 := ih (j+1)
    have h2 := E_even j
    omega

private theorem pow_two_ge_succ (m : Nat) : m+1 ≤ 2^m := by
  induction m with
  | zero => decide
  | succ m ih =>
    rw [Nat.pow_succ]
    omega

/-- A reset from a positive-even sector lands strictly between clean funnels. -/
theorem reset_disjoint (j m : Nat) : E j + 4 ≠ C 0 m := by
  intro h
  have he := E_closed j
  have hc := C_closed 0 m
  simp only [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at hc
  have hp := pow_two_ge_succ m
  have heq : 14 * 2^m = 14 * 2^j + 2*m + 2 := by omega
  by_cases hjm : m ≤ j
  · have hmono : 2^m ≤ 2^j :=
      Nat.pow_le_pow_right (by decide) hjm
    omega
  · have hmono : 2^(j+1) ≤ 2^m :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hmono
    omega

/-- Odd second coordinate stays odd under the recursive G drain. -/
theorem G_odd (k c : Nat) (hc : c%2=1) :
    (G k c).2%2=1 := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
    by_cases h1 : c < 2*k
    · rw [G]
      simp only [h1, dite_true]
      apply ih _ (by omega) _
      omega
    · by_cases h2 : c ≤ 2*k+1
      · rw [G]
        simp only [h1, dite_false, h2, ite_eq_left]
        omega
      · rw [G]
        simp [h1,h2]
        omega

/-- Starting G on an even counter too small for the big branch yields odd c. -/
theorem G_even_small_odd (k c : Nat)
    (hc : c%2=0) (hsmall : c < 2*k+2) :
    (G k c).2%2=1 := by
  by_cases h : c < 2*k
  · rw [G]
    simp only [h, dite_true]
    apply G_odd
    omega
  · rw [G]
    have h2 : c ≤ 2*k+1 := by omega
    simp [h, h2]

/-- Two accelerated calls, assuming even a and even c, in the big branch. -/
theorem T_grow (a c : Nat) (ha : a % 2 = 0)
    (hc : c % 2 = 0) (hlarge : a + 10 ≤ c) :
    T a c = some (a+3, c-2) ∧
    T (a+3) (c-2) = some (2*a+12, c-a-10) := by
  have hclow : 2 ≤ c := by omega
  have hpar : (a+3) % 2 ≠ 0 := by omega
  have hzero : c-2 ≠ 0 := by omega
  have hone : c-2 ≠ 1 := by omega
  have htwo : c-2 ≠ 2 := by omega
  have hthree : c-2 ≠ 3 := by omega
  have hk : (a+3)/2+1 = a/2+2 := by omega
  have hbound : 2*((a+3)/2+1)+2 ≤ c-4 := by omega
  constructor
  · exact T_even a c ha hclow
  · simp only [T, if_neg hzero, if_neg hone, if_neg hpar,
      if_neg htwo, if_neg hthree]
    have hsub : c-2-2 = c-4 := by omega
    rw [hsub, G_big _ _ hbound]
    simp only [Option.some.injEq]
    have hev : a = 2*(a/2) := by omega
    apply Prod.ext <;> omega

/-- All remaining even-c branches (c>=6) exit the even-c sector on the
    second accelerated call. -/
theorem T_small_exits_even (a c : Nat) (ha : a%2=0)
    (hc : c%2=0) (h6 : 6 ≤ c) (hsmall : c < a+10) :
    ∃ a' c', T (a+3) (c-2) = some (a',c') ∧ c'%2=1 := by
  have hpar : (a+3)%2 ≠ 0 := by omega
  have hzero : c-2 ≠ 0 := by omega
  have hone : c-2 ≠ 1 := by omega
  have htwo : c-2 ≠ 2 := by omega
  have hthree : c-2 ≠ 3 := by omega
  have hsub : c-2-2 = c-4 := by omega
  have hbound : c-4 < 2*((a+3)/2+1)+2 := by omega
  have heven : (c-4)%2=0 := by omega
  have hodd := G_even_small_odd ((a+3)/2+1) (c-4) heven hbound
  refine ⟨(G ((a+3)/2+1) (c-4)).1, (G ((a+3)/2+1) (c-4)).2, ?_, hodd⟩
  simp only [T, if_neg hzero, if_neg hone, if_neg hpar,
    if_neg htwo, if_neg hthree]
  rw [hsub]

theorem T_reset (a : Nat) (ha : a%2=0) :
    T a 2 = some (a+3, 0) ∧ T (a+3) 0 = some (2, a+4) := by
  constructor
  · simpa using (T_even a 2 ha (by omega))
  · simp [T, Nat.add_assoc]

/-- Only paths which remain in the even-c sector (until halting).
    The reset represents T(a,2)->T(a+3,0)->(2,a+4). -/
inductive EvenHalts : Nat → Nat → Prop where
  | gate (a : Nat) : a%2=0 → EvenHalts a 4
  | grow (a c : Nat) : a%2=0 → c%2=0 → a+10≤c →
      EvenHalts (2*a+12) (c-a-10) → EvenHalts a c
  | reset (a : Nat) : a%2=0 → EvenHalts 2 (a+4) → EvenHalts a 2

/-- Within this exact even-sector halting grammar, every state E(j),c
    has c=C(j,n). This rules out all alternate reset-assisted funnels. -/
theorem even_funnel_complete (a c : Nat) (h : EvenHalts a c) :
    ∀ j, a = E j → ∃ n, c = C j n := by
  induction h with
  | gate a ha =>
      intro j hj
      exact ⟨0, rfl⟩
  | grow a c ha hc hlarge hchild ih =>
      intro j hj
      have hnxt : 2*a+12 = E (j+1) := by
        rw [hj]
        rfl
      obtain ⟨n, heq⟩ := ih (j+1) hnxt
      refine ⟨n+1, ?_⟩
      simp only [C]
      omega
  | reset a ha hchild ih =>
      intro j hj
      obtain ⟨n, hcn⟩ := ih 0 (by rfl)
      have hd := reset_disjoint j n
      exfalso
      apply hd
      omega

theorem even_funnel_sound (a c : Nat) (h : EvenHalts a c) :
    Halts a c := by
  induction h with
  | gate a ha =>
      exact Halts.next a 4 (a+3) 2
        (T_even a 4 ha (by omega))
        (Halts.now (a+3) 2 (T_gate a ha))
  | grow a c ha hc hlarge hchild ih =>
      obtain ⟨h1,h2⟩ := T_grow a c ha hc hlarge
      exact Halts.next a c (a+3) (c-2) h1
        (Halts.next (a+3) (c-2) (2*a+12) (c-a-10) h2 ih)
  | reset a ha hchild ih =>
      obtain ⟨h1,h2⟩ := T_reset a ha
      exact Halts.next a 2 (a+3) 0 h1
        (Halts.next (a+3) 0 2 (a+4) h2 ih)

theorem even_funnel_iff (j c : Nat) :
    EvenHalts (E j) c ↔ ∃ n, c = C j n := by
  constructor
  · intro h
    exact even_funnel_complete _ _ h j rfl
  · rintro ⟨n, rfl⟩
    induction n generalizing j with
    | zero => exact EvenHalts.gate (E j) (E_even j)
    | succ n ih =>
        have hc : C j (n+1) % 2 = 0 := C_even j (n+1)
        have hl : E j+10 ≤ C j (n+1) := by
          have hh := C_ge_four (j+1) n
          simp only [C]
          omega
        have hstep : C j (n+1) - E j - 10 = C (j+1) n := by
          simp only [C]
          omega
        apply EvenHalts.grow (E j) (C j (n+1)) (E_even j) hc hl
        rw [hstep]
        have he : 2*E j+12 = E (j+1) := rfl
        rw [he]
        exact ih (j+1)

/-- Literal accelerated T-halting traces whose every hub has even c. -/
inductive EvenHIn : Nat → Nat → Nat → Prop where
  | final (a c : Nat) : c%2=0 → T a c=none → EvenHIn 1 a c
  | cons (steps a c a' c' : Nat) :
      c%2=0 → T a c=some (a',c') → EvenHIn steps a' c' →
      EvenHIn (steps+1) a c

theorem even_in_counter (n a c : Nat) (h : EvenHIn n a c) : c%2=0 := by
  cases h with
  | final _ _ hc _ => exact hc
  | cons _ _ _ _ _ hc _ _ => exact hc

theorem even_in_pos (n a c : Nat) (h : EvenHIn n a c) : 1≤n := by
  cases h with
  | final => omega
  | cons steps _ _ _ _ _ _ hr =>
      have hpos := even_in_pos steps _ _ hr
      omega
termination_by n

theorem even_in_more (n a c : Nat) (h : EvenHIn n a c)
    (ht : T a c ≠ none) : 2≤n := by
  cases h with
  | final _ _ _ hnone => exact False.elim (ht hnone)
  | cons steps _ _ _ _ _ _ hrest =>
      have hpos := even_in_pos steps _ _ hrest
      omega

theorem even_in_pop (k a c b d : Nat)
    (ht : T a c=some (b,d)) (h : EvenHIn (k+1) a c) :
    EvenHIn k b d := by
  cases h with
  | final _ _ _ hnone => simp [ht] at hnone
  | cons _ _ _ b' d' _ ht' rest =>
      have hEq : (b',d')=(b,d) := Option.some.inj (ht'.symm.trans ht)
      obtain ⟨hb,hd⟩ := Prod.mk.inj hEq
      subst b'
      subst d'
      exact rest

theorem even_in_tail (n a c b d : Nat)
    (hn : 2≤n) (ht : T a c=some (b,d)) (h : EvenHIn n a c) :
    EvenHIn (n-1) b d := by
  have hEq : (n-1)+1=n := by omega
  have h' : EvenHIn ((n-1)+1) a c := by simpa only [hEq] using h
  exact even_in_pop _ _ _ _ _ ht h'

/-- Exhaustive characterization of genuinely halting T-trajectories that
    remain in even-c hubs throughout, when starting at E(j). -/
theorem even_trace_complete (n a c : Nat) (ha : a%2=0)
    (h : EvenHIn n a c) : EvenHalts a c := by
  induction n using Nat.strongRecOn generalizing a c with
  | ind n ih =>
    have hc : c%2=0 := even_in_counter n a c h
    by_cases h0 : c=0
    · subst c
      have ht : T a 0 = some (2,a+1) := by simp [T]
      have hn : 2≤n := even_in_more n a 0 h (by simp [ht])
      have ht' := even_in_tail n a 0 2 (a+1) hn ht h
      have hceven := even_in_counter (n-1) 2 (a+1) ht'
      omega
    · by_cases h2 : c=2
      · subst c
        obtain ⟨ht1,ht2⟩ := T_reset a ha
        have hn : 2≤n := even_in_more n a 2 h (by simp [ht1])
        have hrest := even_in_tail n a 2 (a+3) 0 hn ht1 h
        have hn2 : 2≤n-1 := even_in_more (n-1) (a+3) 0 hrest (by simp [ht2])
        have hr2 := even_in_tail (n-1) (a+3) 0 2 (a+4) hn2 ht2 hrest
        have hchild : EvenHalts 2 (a+4) := ih (n-2) (by omega) 2 (a+4) (by decide) (by simpa [Nat.sub_sub] using hr2)
        exact EvenHalts.reset a ha hchild
      · by_cases h4 : c=4
        · subst c
          exact EvenHalts.gate a ha
        · have h6 : 6≤c := by omega
          have ht1 := T_even a c ha (by omega)
          have hn : 2≤n := even_in_more n a c h (by simp [ht1])
          have hrest := even_in_tail n a c (a+3) (c-2) hn ht1 h
          by_cases hlarge : a+10≤c
          · obtain ⟨_,ht2⟩ := T_grow a c ha hc hlarge
            have hn2 : 2≤n-1 := even_in_more (n-1) (a+3) (c-2) hrest (by simp [ht2])
            have hr2 := even_in_tail (n-1) (a+3) (c-2) (2*a+12) (c-a-10) hn2 ht2 hrest
            have hchild : EvenHalts (2*a+12) (c-a-10) :=
              ih (n-2) (by omega) _ _ (by omega) (by simpa [Nat.sub_sub] using hr2)
            exact EvenHalts.grow a c ha hc hlarge hchild
          · obtain ⟨b,d,ht2,hodd⟩ := T_small_exits_even a c ha hc h6 (by omega)
            have hn2 : 2≤n-1 := even_in_more (n-1) (a+3) (c-2) hrest (by simp [ht2])
            have hr2 := even_in_tail (n-1) (a+3) (c-2) b d hn2 ht2 hrest
            have hceven := even_in_counter (n-2) b d (by simpa [Nat.sub_sub] using hr2)
            omega

/-- Every certificate in the even-sector grammar is a real T trace, all
    of whose hub configurations have an even second coordinate. -/
theorem even_funnel_trace (a c : Nat) (h : EvenHalts a c) :
    ∃ steps, EvenHIn steps a c := by
  induction h with
  | gate a ha =>
      have ht1 := T_even a 4 ha (by omega)
      have ht2 := T_gate a ha
      exact ⟨2, EvenHIn.cons 1 a 4 (a+3) 2 (by decide) ht1
        (EvenHIn.final (a+3) 2 (by decide) ht2)⟩
  | grow a c ha hc hlarge hchild ih =>
      obtain ⟨steps, hsteps⟩ := ih
      obtain ⟨ht1,ht2⟩ := T_grow a c ha hc hlarge
      refine ⟨steps+2, ?_⟩
      exact EvenHIn.cons (steps+1) a c (a+3) (c-2) hc ht1
        (EvenHIn.cons steps (a+3) (c-2) (2*a+12) (c-a-10)
        (by omega) ht2 hsteps)
  | reset a ha hchild ih =>
      obtain ⟨steps,hsteps⟩ := ih
      obtain ⟨ht1,ht2⟩ := T_reset a ha
      refine ⟨steps+2, ?_⟩
      exact EvenHIn.cons (steps+1) a 2 (a+3) 0 (by decide) ht1
        (EvenHIn.cons steps (a+3) 0 2 (a+4) (by decide) ht2 hsteps)

/-- The only even-c halting traces starting at (2,c) are the C(0,n) family. -/
theorem even_trace_from_two_iff (n c : Nat) :
    EvenHIn n 2 c → ∃ m, c=C 0 m := by
  intro h
  have ht := even_trace_complete n 2 c (by decide) h
  exact even_funnel_complete _ _ ht 0 rfl

/-- Complete classification of synthetic P1(a,0) states that halt **before
    encountering any odd-c hub**. The exact family A_n is both necessary
    and sufficient. Later excursions are outside this theorem's scope. -/
theorem even_trace_from_zero_iff (a : Nat) :
    (∃ steps, EvenHIn steps a 0) ↔ (∃ n, a = C 0 n-1) := by
  constructor
  · rintro ⟨steps, hs⟩
    have ht : T a 0 = some (2,a+1) := by simp [T]
    have hn : 2≤steps := even_in_more steps a 0 hs (by simp [ht])
    have htail := even_in_tail steps a 0 2 (a+1) hn ht hs
    obtain ⟨n,heq⟩ := even_trace_from_two_iff (steps-1) (a+1) htail
    have hc := C_ge_four 0 n
    exact ⟨n, by omega⟩
  · rintro ⟨n,rfl⟩
    have hs : EvenHalts (E 0) (C 0 n) :=
      (even_funnel_iff 0 (C 0 n)).mpr ⟨n,rfl⟩
    obtain ⟨steps,htrace⟩ := even_funnel_trace (E 0) (C 0 n) hs
    have hc := C_ge_four 0 n
    have ht : T (C 0 n-1) 0 = some (2,C 0 n) := by
      simp only [T, ite_true]
      have heq : C 0 n-1+1=C 0 n := by omega
      rw [heq]
    exact ⟨steps+1, EvenHIn.cons steps (C 0 n-1) 0 2 (C 0 n)
      (by decide) ht htrace⟩

#print axioms BB6.HaltingFunnel.even_trace_from_two_iff
#print axioms BB6.HaltingFunnel.even_trace_from_zero_iff
end BB6.HaltingFunnel
