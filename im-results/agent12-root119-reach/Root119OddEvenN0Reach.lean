import Root119Gate
import Root119PrefixShield

namespace BB6Root119

/--
A small reachability invariant separating two local configurations:
an A0 head with 0,1 to its left and a blank immediately to its right,
and a B0 head with left context 101 and a blank immediately to its right.

The second clause excludes the n = 0 instance of the odd-even prefix
preconditions from blank-reachable configurations.
-/
def Agent12ReachInvariant (c : Conf) : Prop :=
  (c.q = .A → c.tape c.h = false → c.tape (c.h-1) = false →
    c.tape (c.h-2) = true → c.tape (c.h+1) = false → False) ∧
  (c.q = .B → c.tape c.h = false → c.tape (c.h-1) = true →
    c.tape (c.h-2) = false → c.tape (c.h-3) = true →
    c.tape (c.h+1) = false → False)

theorem reachable_A_B0_local_invariant (c : Conf) (hr : Reach c) :
    Agent12ReachInvariant c := by
  induction hr with
  | initial =>
      constructor
      · intro hq h0 hleft1 hleft2 hright1
        simp [blank] at hleft2
      · intro hq h0 hleft1 hleft2 hleft3 hright1
        simp [blank] at hq
  | @follow u v hu hstep ih =>
      constructor
      · intro hvq hv0 hvleft1 hvleft2 hvright1
        rcases u with ⟨q,k,t⟩
        have hqE : q = .E := by
          have h := to_A hstep hvq
          simpa using h
        cases hqE
        cases hb : t k with
        | false =>
          simp [next,hb] at hstep
          cases hstep
          have hne : k+1-1 = k := by omega
          simp [setBit,hne] at hvleft1
        | true =>
          simp [next,hb] at hstep
          cases hstep
          have hne : k-1+1 = k := by omega
          simp [setBit,hne] at hvright1
      · intro hvq hv0 hvleft1 hvleft2 hvleft3 hvright1
        rcases u with ⟨q,k,t⟩
        cases q with
        | A =>
          cases hb : t k with
          | true => simp_all [next,hb]
          | false =>
            simp [next,hb] at hstep
            cases hstep
            have heq1 : k+1-2 = k-1 := by omega
            have heq2 : k+1-3 = k-2 := by omega
            have hne1 : k-1 ≠ k := by omega
            have hne2 : k-2 ≠ k := by omega
            have hne3 : k+1 ≠ k := by omega
            have huLeft1 : t (k-1) = false := by
              simpa [setBit,heq1,hne1] using hvleft2
            have huLeft2 : t (k-2) = true := by
              simpa [setBit,heq2,hne2] using hvleft3
            have huRight : t (k+1) = false := by
              simpa [setBit,hne3] using hv0
            exact ih.1 rfl hb huLeft1 huLeft2 huRight
        | F =>
          cases hb : t k with
          | true =>
            simp [next,hb] at hstep
            cases hstep
            cases hvq
          | false =>
            simp [next,hb] at hstep
            cases hstep
            have hne : k-1+1 = k := by omega
            simp [setBit,hne] at hvright1
        | B => cases hb : t k <;> simp [next,hb] at hstep <;> cases hstep <;> cases hvq
        | C => cases hb : t k <;> simp [next,hb] at hstep <;> cases hstep <;> cases hvq
        | D => cases hb : t k <;> simp [next,hb] at hstep <;> cases hstep <;> cases hvq
        | E => cases hb : t k <;> simp [next,hb] at hstep <;> cases hstep <;> cases hvq

theorem Reach_no_B0_oddEven_n0 (c : Conf) (hr : Reach c)
    (hq : c.q = .B) (h0 : c.tape c.h = false)
    (hleft1 : c.tape (c.h-1) = true)
    (hleft2 : c.tape (c.h-2) = false)
    (hleft3 : c.tape (c.h-3) = true)
    (hright1 : c.tape (c.h+1) = false) : False := by
  exact (reachable_A_B0_local_invariant c hr).2
    hq h0 hleft1 hleft2 hleft3 hright1

/-- The synthetic n = 0 shield counterexample is not blank-reachable. -/
theorem oddEvenShieldCounterexample_notReach :
    ¬ Reach oddEvenShieldCounterexample := by
  intro hR
  exact Reach_no_B0_oddEven_n0 oddEvenShieldCounterexample hR rfl
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])
    (by simp [oddEvenShieldCounterexample,oddEvenShieldCounterexampleTape])

#print axioms reachable_A_B0_local_invariant
#print axioms Reach_no_B0_oddEven_n0
#print axioms oddEvenShieldCounterexample_notReach

end BB6Root119
