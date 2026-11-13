import Low42Delta
import NoFatalGuard
import NoFatalRunConverse

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429Low42NoFatal

open BB429OddExcursion BB429SourceE1Delta BB429Low42
open BB429FinishScanEDelta BB429NoFatalGuard

/-- Project a successful signed source instruction to the ordinary
    zipper instruction. -/
theorem oneWithDelta_to_one (c d : Zipper) (delta : Int)
    (h : oneWithDelta c = some (d, delta)) :
    one c = some d := by
  cases hact : action c.state c.current with
  | none =>
      simp [oneWithDelta, hact] at h
  | some a =>
      rcases a with ⟨s, w, rightward⟩
      cases hone : one c with
      | none =>
          simp [oneWithDelta, hact, hone] at h
      | some d' =>
          have hp : (d', if rightward then (1 : Int) else -1) =
              (d, delta) := by
            simpa [oneWithDelta, hact, hone] using h
          have hd : d' = d := congrArg Prod.fst hp
          subst d'
          exact hone

/-- Forgetting the signed displacement of a successful runWithDelta trace
    yields the exact ordinary source zipper run. -/
theorem runWithDelta_to_run
    (n : Nat) (c : Zipper) (q : Zipper × Int)
    (h : runWithDelta n c = some q) :
    BB429OddExcursion.run n c = some q.1 := by
  induction n generalizing c q with
  | zero =>
      have hp : (c, (0 : Int)) = q := by
        exact Option.some.inj (by
          simpa [BB429SourceE1Delta.runWithDelta] using h)
      have hfirst : c = q.1 := congrArg Prod.fst hp
      simp [BB429OddExcursion.run, hfirst]
  | succ n ih =>
      cases hs : oneWithDelta c with
      | none =>
          simp [BB429SourceE1Delta.runWithDelta, hs] at h
      | some p =>
          have hone : one c = some p.1 :=
            oneWithDelta_to_one c p.1 p.2 hs
          cases ht : runWithDelta n p.1 with
          | none =>
              simp [BB429SourceE1Delta.runWithDelta, hs, ht] at h
          | some r =>
              have hp : (r.1, p.2 + r.2) = q := by
                exact Option.some.inj (by
                  simpa [BB429SourceE1Delta.runWithDelta, hs, ht] using h)
              have hr : BB429OddExcursion.run n p.1 = some r.1 :=
                ih p.1 r ht
              have hfirst : r.1 = q.1 := congrArg Prod.fst hp
              simp [BB429OddExcursion.run, hone, hr, hfirst]

/-- Every parameterized low42 source return from its exact post-bubble
    stage is C/01-free through the endpoint. This is a prepared-stage
    source theorem; the preceding J-tape bubble prefix is separate. -/
theorem low42_source_all_no_fatal (j k : Nat) :
    runNoFatal (20*j+18*k+79) (stage42 j k) =
      some (junc 0 0 (4*j+4*k+12)) := by
  exact BB429NoFatalRunConverse.runNoFatal_of_run_live
    (20*j+18*k+79) (stage42 j k)
    (junc 0 0 (4*j+4*k+12))
    (runWithDelta_to_run (20*j+18*k+79) (stage42 j k)
      (junc 0 0 (4*j+4*k+12), -((4*j+4*k+5 : Nat) : Int))
      (low42_source_all j k))
    (by simp [BB429NoFatalGuard.fatalCZero, junc, z])
    (by simp [one, action, junc, z])

#print axioms oneWithDelta_to_one
#print axioms runWithDelta_to_run
#print axioms low42_source_all_no_fatal

end BB429Low42NoFatal
