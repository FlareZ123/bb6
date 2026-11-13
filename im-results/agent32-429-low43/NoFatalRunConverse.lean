import NoFatalGuard

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429NoFatalRunConverse

open BB429OddExcursion BB429NoFatalGuard

/-- A fatal C/01 zipper has exactly one defined transition, to D/1,
    after which the original source interpreter has no next transition. -/
theorem fatalCZero_one_halts (c : Zipper)
    (hf : fatalCZero c = true) :
    ∃ d : Zipper, one c = some d ∧ one d = none := by
  cases c with
  | mk s l b r =>
    cases s with
    | zero => simp [fatalCZero] at hf
    | succ s =>
      cases s with
      | zero => simp [fatalCZero] at hf
      | succ s =>
        cases s with
        | zero =>
          cases b with
          | true => simp [fatalCZero] at hf
          | false =>
            cases r with
            | nil => simp [fatalCZero] at hf
            | cons a rs =>
              cases a with
              | false => simp [fatalCZero] at hf
              | true =>
                refine ⟨z 3 (false :: l) true rs, ?_, ?_⟩
                · simp [BB429OddExcursion.one, BB429OddExcursion.action]
                · simp [BB429OddExcursion.one, BB429OddExcursion.action]
        | succ s => simp [fatalCZero] at hf

/-- Converse guard theorem: if the ordinary original-source run succeeds
    and ends at a live, nonfatal configuration, it cannot have crossed the
    fatal C/01 gateway. Hence the guarded interpreter accepts the same run.

    The endpoint hypotheses are essential: a run may stop exactly at D/1
    immediately after a fatal C/01 transition, or may end at a fatal C/01
    configuration itself. -/
theorem runNoFatal_of_run_live
    (n : Nat) (z0 zf : Zipper)
    (hrun : BB429OddExcursion.run n z0 = some zf)
    (hsafe : fatalCZero zf = false)
    (hlive : one zf ≠ none) :
    runNoFatal n z0 = some zf := by
  induction n generalizing z0 zf with
  | zero =>
      have hEq : z0 = zf := by
        simpa [BB429OddExcursion.run] using hrun
      subst zf
      simp [runNoFatal, hsafe]
  | succ n ih =>
      cases hf : fatalCZero z0 with
      | false =>
          cases hstep : one z0 with
          | none =>
              simp [BB429OddExcursion.run, hstep] at hrun
          | some d =>
              have htail : BB429OddExcursion.run n d = some zf := by
                simpa [BB429OddExcursion.run, hstep] using hrun
              have hguard := ih d zf htail hsafe hlive
              simp [runNoFatal, hf, hstep, hguard]
      | true =>
          obtain ⟨d, hstep, hhalt⟩ := fatalCZero_one_halts z0 hf
          have htail : BB429OddExcursion.run n d = some zf := by
            simpa [BB429OddExcursion.run, hstep] using hrun
          cases n with
          | zero =>
              have hd : d = zf := by
                simpa [BB429OddExcursion.run] using htail
              subst zf
              exact False.elim (hlive hhalt)
          | succ n =>
              simp [BB429OddExcursion.run, hhalt] at htail

#print axioms fatalCZero_one_halts
#print axioms runNoFatal_of_run_live

end BB429NoFatalRunConverse
