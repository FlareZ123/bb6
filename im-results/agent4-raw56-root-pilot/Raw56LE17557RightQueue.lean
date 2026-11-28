import Lean.Elab.Tactic.Omega

/-!
  A source-derived right-run queue for Raw56 leaf 17557.

  A queue stores the positive lengths of the finite right-hand one-runs.
  `more a g tail` means a-run, then a finite zero-gap of length g, then tail;
  `final a` means the last finite one-run followed by the infinite blank ray.

  The local source triads have the following exact queue effects:
    A-normal: [a,b,c,...] -> [2,c+5,...]
    A-carry:  [a,5,c,...] -> [a+d+4,c+5,...]
    B:        [a,b,...]   -> [2,5,b+3,...]

  The invariant below captures the observed *positional* residue law:
    gap 0 is 1;
    gap 1 is 1 or is >=5 with residue 1 or 5 mod 8;
    every later gap has residue 3 or 7 mod 8;
    the first one-run has residue 2 or 6 mod 8.
  In addition, if a second gap exists then the second run has length >=5.
  These conditions are closed under all three source-derived queue effects,
  provided every A-carry's left one-run d is divisible by 4.

  This is an all-finite-prefix theorem for the right-run transducer, not yet
  the full original-machine nonhalting theorem. The remaining integration is
  to pair it with the accepted left-frame schedule and compose the exact
  LocalSweeps source rewrites.
-/

namespace BB6.Agent4Raw56LE17557RightQueue

inductive Queue where
  | final (ones : Nat)
  | more (ones gap : Nat) (tail : Queue)
  deriving Repr, DecidableEq

inductive Kind where
  | normal
  | carry
  | b
  deriving Repr, DecidableEq

/-- All runs from the third onward are positive and every gap from the
    third onward is 3 or 7 modulo eight. -/
def GoodTail : Queue → Prop
  | .final a => 0 < a
  | .more a g tail =>
      0 < a ∧ (g % 8 = 3 ∨ g % 8 = 7) ∧ GoodTail tail

/-- The event-boundary right queue invariant. The first finite gap is one.
    The second gap is either one (an A event) or at least five in residue
    class 1/5 (a B event). -/
def Good : Queue → Prop
  | .more a 1 (.final b) =>
      (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 0 < b
  | .more a 1 (.more b g tail) =>
      (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 5 ≤ b ∧
      (g = 1 ∨ ((g % 8 = 1 ∨ g % 8 = 5) ∧ 5 ≤ g)) ∧
      GoodTail tail
  | _ => False

/-- Exact right-run rewrite for a normal A triad, with a final third run. -/
theorem normal_final_good (c : Nat) (hc : 0 < c) :
    Good (.more 2 1 (.final (c+5))) := by
  simp [Good]
  omega

/-- Exact right-run rewrite for a normal A triad, with a nonfinal third run. -/
theorem normal_more_good (c g : Nat) (tail : Queue)
    (hc : 0 < c) (hg : g % 8 = 3 ∨ g % 8 = 7)
    (ht : GoodTail tail) :
    Good (.more 2 1 (.more (c+5) (g-2) tail)) := by
  have hgap : (g-2 = 1) ∨
      (((g-2) % 8 = 1 ∨ (g-2) % 8 = 5) ∧ 5 ≤ g-2) := by omega
  change (2 % 8 = 2 ∨ 2 % 8 = 6) ∧ 0 < 2 ∧ 5 ≤ c+5 ∧
    ((g-2 = 1) ∨ (((g-2) % 8 = 1 ∨ (g-2) % 8 = 5) ∧ 5 ≤ g-2)) ∧
    GoodTail tail
  exact ⟨by omega, by omega, by omega, hgap, ht⟩

/-- A carry's first output run retains residue 2/6 when its left one-run
    d is divisible by four. -/
theorem carry_first_residue (a d : Nat)
    (ha : a % 8 = 2 ∨ a % 8 = 6) (hd : d % 4 = 0) :
    (a+d+4) % 8 = 2 ∨ (a+d+4) % 8 = 6 := by
  omega

/-- Exact right-run rewrite for a carry A triad, with a final third run. -/
theorem carry_final_good (a d c : Nat)
    (ha : a % 8 = 2 ∨ a % 8 = 6) (hd : d % 4 = 0)
    (hc : 0 < c) :
    Good (.more (a+d+4) 1 (.final (c+5))) := by
  have hr := carry_first_residue a d ha hd
  change ((a+d+4) % 8 = 2 ∨ (a+d+4) % 8 = 6) ∧
    0 < a+d+4 ∧ 0 < c+5
  exact ⟨hr, by omega, by omega⟩

/-- Exact right-run rewrite for a carry A triad, with a nonfinal third run. -/
theorem carry_more_good (a d c g : Nat) (tail : Queue)
    (ha : a % 8 = 2 ∨ a % 8 = 6) (hd : d % 4 = 0)
    (hc : 0 < c) (hg : g % 8 = 3 ∨ g % 8 = 7)
    (ht : GoodTail tail) :
    Good (.more (a+d+4) 1 (.more (c+5) (g-2) tail)) := by
  have hr := carry_first_residue a d ha hd
  have hgap : (g-2 = 1) ∨
      (((g-2) % 8 = 1 ∨ (g-2) % 8 = 5) ∧ 5 ≤ g-2) := by omega
  change ((a+d+4) % 8 = 2 ∨ (a+d+4) % 8 = 6) ∧
    0 < a+d+4 ∧ 5 ≤ c+5 ∧
    ((g-2 = 1) ∨ (((g-2) % 8 = 1 ∨ (g-2) % 8 = 5) ∧ 5 ≤ g-2)) ∧
    GoodTail tail
  exact ⟨hr, by omega, by omega, hgap, ht⟩

/-- Subtracting two from a B-event gap leaves a later gap in residue 3/7. -/
theorem b_gap_drop (g : Nat)
    (hgmod : g % 8 = 1 ∨ g % 8 = 5) (hg : 5 ≤ g) :
    3 ≤ g-2 ∧ ((g-2) % 8 = 3 ∨ (g-2) % 8 = 7) := by
  omega

/-- The gap inserted by B is one less than its first input run. -/
theorem b_first_drop (a : Nat)
    (hamod : a % 8 = 2 ∨ a % 8 = 6) (ha : 0 < a) :
    (a-1 = 1) ∨ (((a-1) % 8 = 1 ∨ (a-1) % 8 = 5) ∧ 5 ≤ a-1) := by
  omega

/-- Exact right-run rewrite for a final B triad. -/
theorem b_final_good (a b : Nat)
    (hamod : a % 8 = 2 ∨ a % 8 = 6) (ha : 0 < a) (hb : 0 < b) :
    Good (.more 2 1 (.more 5 (a-1) (.final (b+3)))) := by
  have hgap := b_first_drop a hamod ha
  change (2 % 8 = 2 ∨ 2 % 8 = 6) ∧ 0 < 2 ∧ 5 ≤ 5 ∧
    ((a-1 = 1) ∨ (((a-1) % 8 = 1 ∨ (a-1) % 8 = 5) ∧ 5 ≤ a-1)) ∧
    GoodTail (.final (b+3))
  exact ⟨by omega, by omega, by omega, hgap, by simp [GoodTail]; omega⟩

/-- Exact right-run rewrite for a nonfinal B triad. -/
theorem b_more_good (a b g : Nat) (tail : Queue)
    (hamod : a % 8 = 2 ∨ a % 8 = 6) (ha : 0 < a)
    (hb : 0 < b) (hgmod : g % 8 = 1 ∨ g % 8 = 5)
    (hg : 5 ≤ g) (ht : GoodTail tail) :
    Good (.more 2 1 (.more 5 (a-1) (.more (b+3) (g-2) tail))) := by
  have hfirst := b_first_drop a hamod ha
  have hgap := b_gap_drop g hgmod hg
  have htail : GoodTail (.more (b+3) (g-2) tail) := by
    change 0 < b+3 ∧ ((g-2) % 8 = 3 ∨ (g-2) % 8 = 7) ∧ GoodTail tail
    exact ⟨by omega, hgap.2, ht⟩
  change (2 % 8 = 2 ∨ 2 % 8 = 6) ∧ 0 < 2 ∧ 5 ≤ 5 ∧
    ((a-1 = 1) ∨ (((a-1) % 8 = 1 ∨ (a-1) % 8 = 5) ∧ 5 ≤ a-1)) ∧
    GoodTail (.more (b+3) (g-2) tail)
  exact ⟨by omega, by omega, by omega, hfirst, htail⟩

/-- One physical source triad's right-run effect. The constructors are
    deliberately aligned with A_triad_normal, A_triad_carry, and B_triad. -/
inductive Step : Nat → Queue → Kind → Queue → Prop
  | normalFinal {d a b c : Nat}
      (ha : 0 < a) (hb : 6 ≤ b) (hc : 0 < c) :
      Step d (.more a 1 (.more b 1 (.final c)))
        .normal (.more 2 1 (.final (c+5)))
  | normalMore {d a b c g : Nat} {tail : Queue}
      (ha : 0 < a) (hb : 6 ≤ b) (hc : 0 < c)
      (hg : g % 8 = 3 ∨ g % 8 = 7) :
      Step d (.more a 1 (.more b 1 (.more c g tail)))
        .normal (.more 2 1 (.more (c+5) (g-2) tail))
  | carryFinal {d a c : Nat}
      (ha : 0 < a) (hc : 0 < c) (hd : d % 4 = 0) :
      Step d (.more a 1 (.more 5 1 (.final c)))
        .carry (.more (a+d+4) 1 (.final (c+5)))
  | carryMore {d a c g : Nat} {tail : Queue}
      (ha : 0 < a) (hc : 0 < c) (hd : d % 4 = 0)
      (hg : g % 8 = 3 ∨ g % 8 = 7) :
      Step d (.more a 1 (.more 5 1 (.more c g tail)))
        .carry (.more (a+d+4) 1 (.more (c+5) (g-2) tail))
  | bFinal {d a b : Nat}
      (ha : 2 ≤ a) (hb : 0 < b) :
      Step d (.more a 1 (.final b))
        .b (.more 2 1 (.more 5 (a-1) (.final (b+3))))
  | bMore {d a b g : Nat} {tail : Queue}
      (ha : 2 ≤ a) (hb : 0 < b) (hgmod : g % 8 = 1 ∨ g % 8 = 5)
      (hg : 5 ≤ g) :
      Step d (.more a 1 (.more b g tail))
        .b (.more 2 1 (.more 5 (a-1) (.more (b+3) (g-2) tail)))

/-- A good queue always has a next source-derived triad, and its successor
    is again good, for every carry length divisible by four. -/
theorem good_step (q : Queue) (d : Nat) (hd : d % 4 = 0)
    (hq : Good q) :
    ∃ k q', Step d q k q' ∧ Good q' := by
  cases q with
  | final a =>
      simp [Good] at hq
  | more a g0 rest =>
      cases g0 with
      | zero =>
          simp [Good] at hq
      | succ g0 =>
          cases g0 with
          | succ g0 =>
              simp [Good] at hq
          | zero =>
              cases rest with
              | final b =>
                  have h : (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 0 < b := by
                    simpa [Good] using hq
                  rcases h with ⟨ha, haPos, hbPos⟩
                  refine ⟨.b, .more 2 1 (.more 5 (a-1) (.final (b+3))), ?_, ?_⟩
                  · exact Step.bFinal (by omega) hbPos
                  · exact b_final_good a b ha haPos hbPos
              | more b g tail =>
                  have h :
                      (a % 8 = 2 ∨ a % 8 = 6) ∧ 0 < a ∧ 5 ≤ b ∧
                      (g = 1 ∨ ((g % 8 = 1 ∨ g % 8 = 5) ∧ 5 ≤ g)) ∧
                      GoodTail tail := by
                    simpa [Good] using hq
                  rcases h with ⟨ha, haPos, hb, hg, hTail⟩
                  by_cases hg1 : g = 1
                  · subst g
                    cases tail with
                    | final c =>
                        have hc : 0 < c := by
                          simpa [GoodTail] using hTail
                        by_cases hb5 : b = 5
                        · refine ⟨.carry, .more (a+d+4) 1 (.final (c+5)), ?_, ?_⟩
                          · exact Step.carryFinal haPos hc hd
                          · exact carry_final_good a d c ha hd hc
                        · have hb6 : 6 ≤ b := by omega
                          refine ⟨.normal, .more 2 1 (.final (c+5)), ?_, ?_⟩
                          · exact Step.normalFinal haPos hb6 hc
                          · exact normal_final_good c hc
                    | more c g2 tail2 =>
                        have ht : 0 < c ∧ (g2 % 8 = 3 ∨ g2 % 8 = 7) ∧
                            GoodTail tail2 := by
                          simpa [GoodTail] using hTail
                        rcases ht with ⟨hc, hg2, hTail2⟩
                        by_cases hb5 : b = 5
                        · refine ⟨.carry,
                            .more (a+d+4) 1 (.more (c+5) (g2-2) tail2), ?_, ?_⟩
                          · exact Step.carryMore haPos hc hd hg2
                          · exact carry_more_good a d c g2 tail2 ha hd hc hg2 hTail2
                        · have hb6 : 6 ≤ b := by omega
                          refine ⟨.normal,
                            .more 2 1 (.more (c+5) (g2-2) tail2), ?_, ?_⟩
                          · exact Step.normalMore haPos hb6 hc hg2
                          · exact normal_more_good c g2 tail2 hc hg2 hTail2
                  · have hgap : (g % 8 = 1 ∨ g % 8 = 5) ∧ 5 ≤ g := by
                      rcases hg with h | h
                      · exact False.elim (hg1 h)
                      · exact h
                    refine ⟨.b,
                      .more 2 1 (.more 5 (a-1) (.more (b+3) (g-2) tail)), ?_, ?_⟩
                    · exact Step.bMore (by omega) (by omega) hgap.1 hgap.2
                    · exact b_more_good a b g tail ha haPos (by omega)
                        hgap.1 hgap.2 hTail

/-- The right-run relation can be iterated for arbitrarily many source
    triads. The only external parameter is the left carry-run length d_n;
    requiring d_n divisible by four is sufficient for closure. -/
inductive Run (carry : Nat → Nat) : Nat → Queue → Queue → Prop
  | zero (q : Queue) : Run carry 0 q q
  | step {n : Nat} {q r s : Queue} {k : Kind}
      (hr : Run carry n q r)
      (hs : Step (carry n) r k s) :
      Run carry (n+1) q s

theorem run_safe (carry : Nat → Nat)
    (hcarry : ∀ n, carry n % 4 = 0) :
    ∀ n q, Good q → ∃ r, Run carry n q r ∧ Good r := by
  intro n
  induction n with
  | zero =>
      intro q hq
      exact ⟨q, Run.zero q, hq⟩
  | succ n ih =>
      intro q hq
      obtain ⟨r, hr, hgood⟩ := ih q hq
      obtain ⟨k, s, hs, hgood'⟩ := good_step r (carry n) (hcarry n) hgood
      exact ⟨s, Run.step hr hs, hgood'⟩

def initial : Queue := .more 2 1 (.more 5 1 (.final 7))

theorem initial_good : Good initial := by
  decide

/-- Every finite prefix of the right-run execution from the C₂ checkpoint
    exists and remains inside the source-triad guard domain. -/
theorem every_finite_prefix (carry : Nat → Nat)
    (hcarry : ∀ n, carry n % 4 = 0) (n : Nat) :
    ∃ q, Run carry n initial q ∧ Good q := by
  exact run_safe carry hcarry n initial initial_good

#print axioms normal_final_good
#print axioms normal_more_good
#print axioms carry_final_good
#print axioms carry_more_good
#print axioms b_final_good
#print axioms b_more_good
#print axioms good_step
#print axioms run_safe
#print axioms every_finite_prefix

end BB6.Agent4Raw56LE17557RightQueue
