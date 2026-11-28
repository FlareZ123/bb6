import Raw56LE17557RightQueue

namespace BB6.Agent4Raw56LE17557CarryStack

open BB6.Agent4Raw56LE17557RightQueue

/-- The source A-normal sweep creates a left one-run of length
    (first right-run length)+2. B preserves older one-runs; A-carry
    consumes the top one-run (or the empty run of length zero at the base). -/
def StackGood (s : List Nat) : Prop :=
  ∀ d, d ∈ s → d % 4 = 0

/-- The first right-run residue is part of every good event-boundary queue. -/
theorem good_first_mod8 (a : Nat) (tail : Queue)
    (h : Good (.more a 1 tail)) :
    a % 8 = 2 ∨ a % 8 = 6 := by
  cases tail with
  | final b =>
      have hh : (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 0 < b := by
        simpa [Good] using h
      exact hh.1
  | more b g tail =>
      have hh : (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 5 ≤ b ∧
          (g = 1 ∨ ((g % 8 = 1 ∨ g % 8 = 5) ∧ 5 ≤ g)) ∧
          GoodTail tail := by
        simpa [Good] using h
      exact hh.1

theorem stack_push_good (s : List Nat) (a : Nat)
    (hs : StackGood s) (ha : a % 4 = 2) :
    StackGood ((a+2)::s) := by
  intro d hd
  simp only [List.mem_cons] at hd
  rcases hd with h | h
  · subst d
    omega
  · exact hs d h

theorem stack_tail_good {d : Nat} {s : List Nat}
    (hs : StackGood (d::s)) : StackGood s := by
  intro x hx
  apply hs x
  exact List.mem_cons_of_mem d hx

theorem stack_headD_mod4 (s : List Nat) (hs : StackGood s) :
    (s.headD 0) % 4 = 0 := by
  cases s with
  | nil => simp
  | cons d tail =>
      have hd : d ∈ d::tail := by simp
      simpa using hs d hd

/-- One-run component of the source triads. The d parameter is the
    left one-run length consumed by a carry; for normal/B it is an
    unused carry slot, chosen from the current stack head. -/
inductive StackStep : List Nat → Kind → Nat → List Nat → Prop
  | normal {a d : Nat} {s : List Nat}
      (ha : a % 4 = 2) (hd : d % 4 = 0) :
      StackStep s .normal d ((a+2)::s)
  | b {d : Nat} {s : List Nat}
      (hd : d % 4 = 0) :
      StackStep s .b d s
  | carryEmpty :
      StackStep [] .carry 0 []
  | carryPop {d : Nat} {s : List Nat} :
      StackStep (d::s) .carry d s

/-- The one-run stack transition preserves divisibility by four and
    certifies the carry length. -/
theorem stack_step_safe {s s' : List Nat} {k : Kind} {d : Nat}
    (hs : StackGood s) (h : StackStep s k d s') :
    StackGood s' ∧ d % 4 = 0 := by
  cases h with
  | normal ha hd =>
      exact ⟨stack_push_good s _ hs ha, hd⟩
  | b hd =>
      exact ⟨hs, hd⟩
  | carryEmpty =>
      simp [StackGood]
  | carryPop =>
      have hd : d % 4 = 0 := hs d (by simp)
      exact ⟨stack_tail_good hs, hd⟩

/-- A coupled event is exactly one accepted right-run triad rewrite paired
    with the corresponding one-run effect on the left tape. -/
def CoupledStep (q : Queue) (s : List Nat) (k : Kind) (d : Nat)
    (q' : Queue) (s' : List Nat) : Prop :=
  Step d q k q' ∧ StackStep s k d s'

/-- A good right queue and a four-divisible left one-run stack always admit
    a coupled next triad. In particular, the carry parameter is no longer
    an external hypothesis: it is the top of the one-run stack, or zero. -/
theorem coupled_good_step (q : Queue) (s : List Nat)
    (hq : Good q) (hs : StackGood s) :
    ∃ k d q' s', CoupledStep q s k d q' s' ∧
      Good q' ∧ StackGood s' ∧ d % 4 = 0 := by
  let d := s.headD 0
  have hd : d % 4 = 0 := by
    simpa [d] using stack_headD_mod4 s hs
  obtain ⟨k, q', hStep, hGood'⟩ := good_step q d hd hq
  cases hStep with
  | normalFinal ha hb hc =>
      have hmod8 : a % 8 = 2 ∨ a % 8 = 6 :=
        good_first_mod8 a (.more b 1 (.final c)) hq
      have hmod4 : a % 4 = 2 := by omega
      refine ⟨.normal, d, .more 2 1 (.final (c+5)), (a+2)::s, ?_, ?_, ?_, hd⟩
      · exact ⟨Step.normalFinal ha hb hc, StackStep.normal hmod4 hd⟩
      · exact normal_final_good c hc
      · exact stack_push_good s a hs hmod4
  | normalMore ha hb hc hg =>
      have hmod8 : a % 8 = 2 ∨ a % 8 = 6 :=
        good_first_mod8 a (.more b 1 (.more c g tail)) hq
      have hmod4 : a % 4 = 2 := by omega
      have hshape : GoodTail (.more c g tail) := by
        have hh : (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 5 ≤ b ∧
            (1 = 1 ∨ ((1 % 8 = 1 ∨ 1 % 8 = 5) ∧ 5 ≤ 1)) ∧
            GoodTail (.more c g tail) := by
          simpa [Good] using hq
        exact hh.2.2.2.2
      have ht : 0 < c ∧ (g % 8 = 3 ∨ g % 8 = 7) ∧ GoodTail tail := by
        simpa [GoodTail] using hshape
      refine ⟨.normal, d, .more 2 1 (.more (c+5) (g-2) tail),
        (a+2)::s, ?_, ?_, ?_, hd⟩
      · exact ⟨Step.normalMore ha hb hc hg, StackStep.normal hmod4 hd⟩
      · exact normal_more_good c g tail hc hg ht.2.2
      · exact stack_push_good s a hs hmod4
  | carryFinal ha hc hdc =>
      have hmod8 : a % 8 = 2 ∨ a % 8 = 6 :=
        good_first_mod8 a (.more 5 1 (.final c)) hq
      cases s with
      | nil =>
          have hd0 : d = 0 := by simp [d]
          subst d
          refine ⟨.carry, 0, .more (a+4) 1 (.final (c+5)), [],
            ?_, ?_, ?_, by decide⟩
          · exact ⟨Step.carryFinal ha hc (by decide), StackStep.carryEmpty⟩
          · exact carry_final_good a 0 c hmod8 (by decide) hc
          · simp [StackGood]
      | cons top tail =>
          have hdtop : d = top := by simp [d]
          subst d
          have htop : top % 4 = 0 := hs top (by simp)
          refine ⟨.carry, top, .more (a+top+4) 1 (.final (c+5)), tail,
            ?_, ?_, ?_, htop⟩
          · exact ⟨Step.carryFinal ha hc htop, StackStep.carryPop⟩
          · exact carry_final_good a top c hmod8 htop hc
          · exact stack_tail_good hs
  | carryMore ha hc hdc hg =>
      have hmod8 : a % 8 = 2 ∨ a % 8 = 6 :=
        good_first_mod8 a (.more 5 1 (.more c g tail)) hq
      have hshape : GoodTail (.more c g tail) := by
        have hh : (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 5 ≤ 5 ∧
            (1 = 1 ∨ ((1 % 8 = 1 ∨ 1 % 8 = 5) ∧ 5 ≤ 1)) ∧
            GoodTail (.more c g tail) := by
          simpa [Good] using hq
        exact hh.2.2.2.2
      have ht : 0 < c ∧ (g % 8 = 3 ∨ g % 8 = 7) ∧ GoodTail tail := by
        simpa [GoodTail] using hshape
      cases s with
      | nil =>
          have hd0 : d = 0 := by simp [d]
          subst d
          refine ⟨.carry, 0, .more (a+4) 1 (.more (c+5) (g-2) tail), [],
            ?_, ?_, ?_, by decide⟩
          · exact ⟨Step.carryMore ha hc (by decide) hg, StackStep.carryEmpty⟩
          · exact carry_more_good a 0 c g tail hmod8 (by decide) hc hg ht.2.2
          · simp [StackGood]
      | cons top tailStack =>
          have hdtop : d = top := by simp [d]
          subst d
          have htop : top % 4 = 0 := hs top (by simp)
          refine ⟨.carry, top, .more (a+top+4) 1 (.more (c+5) (g-2) tail),
            tailStack, ?_, ?_, ?_, htop⟩
          · exact ⟨Step.carryMore ha hc htop hg, StackStep.carryPop⟩
          · exact carry_more_good a top c g tail hmod8 htop hc hg ht.2.2
          · exact stack_tail_good hs
  | bFinal ha hb =>
      have hmod8 : a % 8 = 2 ∨ a % 8 = 6 :=
        good_first_mod8 a (.final b) hq
      refine ⟨.b, d, .more 2 1 (.more 5 (a-1) (.final (b+3))), s,
        ?_, ?_, hs, hd⟩
      · exact ⟨Step.bFinal ha hb, StackStep.b hd⟩
      · exact b_final_good a b hmod8 (by omega) hb
  | bMore ha hb hgmod hg =>
      have hmod8 : a % 8 = 2 ∨ a % 8 = 6 :=
        good_first_mod8 a (.more b g tail) hq
      have hshape : GoodTail tail := by
        have hh : (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 5 ≤ b ∧
            (g = 1 ∨ ((g % 8 = 1 ∨ g % 8 = 5) ∧ 5 ≤ g)) ∧
            GoodTail tail := by
          simpa [Good] using hq
        exact hh.2.2.2.2
      refine ⟨.b, d,
        .more 2 1 (.more 5 (a-1) (.more (b+3) (g-2) tail)), s,
        ?_, ?_, hs, hd⟩
      · exact ⟨Step.bMore ha hb hgmod hg, StackStep.b hd⟩
      · exact b_more_good a b g tail hmod8 (by omega) hb hgmod hg hshape

/-- A finite execution of coupled right-run and left one-run transitions. -/
inductive Run : Nat → Queue → List Nat → Queue → List Nat → Prop
  | zero (q : Queue) (s : List Nat) : Run 0 q s q s
  | step {n : Nat} {q r q' : Queue} {s t s' : List Nat} {k : Kind} {d : Nat}
      (hr : Run n q s r t)
      (hs : CoupledStep r t k d q' s') :
      Run (n+1) q s q' s'

theorem run_safe :
    ∀ n q s, Good q → StackGood s →
      ∃ q' s', Run n q s q' s' ∧ Good q' ∧ StackGood s' := by
  intro n
  induction n with
  | zero =>
      intro q s hq hs
      exact ⟨q, s, Run.zero q s, hq, hs⟩
  | succ n ih =>
      intro q s hq hs
      obtain ⟨r, t, hr, hR, hT⟩ := ih q s hq hs
      obtain ⟨k, d, q', s', hStep, hGood', hStack', hd⟩ :=
        coupled_good_step r t hR hT
      exact ⟨q', s', Run.step hr hStep, hGood', hStack'⟩

/-- From the C₂ right queue and an empty left one-run stack, every finite
    coupled prefix exists. Every carry consumes either zero or a multiple
    of four, and every normal sweep pushes a multiple of four. -/
theorem every_coupled_prefix (n : Nat) :
    ∃ q s, Run n initial [] q s ∧ Good q ∧ StackGood s := by
  exact run_safe n initial [] initial_good (by simp [StackGood])

#print axioms stack_step_safe
#print axioms coupled_good_step
#print axioms run_safe
#print axioms every_coupled_prefix

end BB6.Agent4Raw56LE17557CarryStack
