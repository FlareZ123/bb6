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
  simp [hx]

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

/-- The first finite one-run length of a queue. -/
def firstRun : Queue → Nat
  | .final a => a
  | .more a _ _ => a

/-- A good event-boundary queue has first run 2 modulo four. -/
theorem firstRun_mod4_of_good (q : Queue) (hq : Good q) :
    firstRun q % 4 = 2 := by
  cases q with
  | final a =>
      simp [Good] at hq
  | more a g tail =>
      cases g with
      | zero =>
          simp [Good] at hq
      | succ g =>
          cases g with
          | zero =>
              have hmod8 := good_first_mod8 a tail hq
              omega
          | succ g =>
              simp [Good] at hq

/-- The one-run stack update dictated by the source triad kind. -/
def stackUpdate (q : Queue) (s : List Nat) (k : Kind) : List Nat :=
  match k with
  | .normal => (firstRun q + 2)::s
  | .b => s
  | .carry => s.tail

/-- A good right queue and a four-divisible left one-run stack always admit
    a coupled next triad. The carry parameter is the top of the one-run
    stack, or zero when that stack is empty; it is therefore divisible by 4. -/
theorem coupled_good_step (q : Queue) (s : List Nat)
    (hq : Good q) (hs : StackGood s) :
    ∃ k d q' s', CoupledStep q s k d q' s' ∧
      Good q' ∧ StackGood s' ∧ d % 4 = 0 := by
  let d := s.headD 0
  have hd : d % 4 = 0 := by
    simpa [d] using stack_headD_mod4 s hs
  obtain ⟨k, q', hStep, hGood'⟩ := good_step q d hd hq
  let s' := stackUpdate q s k
  have hStack : StackStep s k d s' := by
    cases k with
    | normal =>
        have hmod4 : firstRun q % 4 = 2 := firstRun_mod4_of_good q hq
        simp [s', stackUpdate]
        exact StackStep.normal hmod4 hd
    | b =>
        simp [s', stackUpdate]
        exact StackStep.b hd
    | carry =>
        cases s with
        | nil =>
            simp [s', stackUpdate, d]
            exact StackStep.carryEmpty
        | cons top tail =>
            simp [s', stackUpdate, d]
            exact StackStep.carryPop
  have hPres := stack_step_safe hs hStack
  exact ⟨k, d, q', s', ⟨hStep, hStack⟩, hGood', hPres.1, hPres.2⟩

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
