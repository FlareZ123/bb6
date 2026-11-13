import BB429OddExcursion
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429NoFatalGuard

open BB6Coverage BB429OddExcursion

/-- The actual halting gateway is C/0 with a marked cell immediately
    to the right. Harmless C/0/blank-right visits are allowed. -/
def fatalCZero (c : BB429OddExcursion.Zipper) : Bool :=
  c.state == 2 && !c.current && c.right.headD false

/-- Run the original zipper interpreter, rejecting only a C/0 whose
    immediate right neighbor is marked. -/
def runNoFatal : Nat → BB429OddExcursion.Zipper → Option BB429OddExcursion.Zipper
  | 0, c =>
      if fatalCZero c then none else some c
  | n+1, c =>
      if fatalCZero c then none else
        (BB429OddExcursion.one c).bind (runNoFatal n)

/-- A successful guarded run is the exact ordinary original-source run. -/
theorem runNoFatal_to_run (n : Nat) (z z' : BB429OddExcursion.Zipper)
    (hsafe : runNoFatal n z = some z') :
    BB429OddExcursion.run n z = some z' := by
  induction n generalizing z with
  | zero =>
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          simp [runNoFatal, hf] at hsafe
          simpa [BB429OddExcursion.run] using hsafe
  | succ n ih =>
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          cases hstep : BB429OddExcursion.one z with
          | none =>
              simp [runNoFatal, hf, hstep] at hsafe
          | some d =>
              have htail : runNoFatal n d = some z' := by
                simpa [runNoFatal, hf, hstep] using hsafe
              have hrun := ih d z' htail
              simp [BB429OddExcursion.run, hstep, hrun]

/-- Every source configuration through the endpoint of a successful
    guarded run is nonfatal, and every prefix exists in the ordinary
    zipper semantics. -/
theorem runNoFatal_prefix (n t : Nat) (z z' : BB429OddExcursion.Zipper)
    (hsafe : runNoFatal n z = some z') (ht : t ≤ n) :
    ∃ p, BB429OddExcursion.run t z = some p ∧
      fatalCZero p = false := by
  induction n generalizing t z z' with
  | zero =>
      have ht0 : t = 0 := by omega
      subst t
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          simp [runNoFatal, hf] at hsafe
          exact ⟨z, by simp [BB429OddExcursion.run], hf⟩
  | succ n ih =>
      cases hf : fatalCZero z with
      | true =>
          simp [runNoFatal, hf] at hsafe
      | false =>
          by_cases ht0 : t = 0
          · subst t
            exact ⟨z, by simp [BB429OddExcursion.run], hf⟩
          · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := by omega
            have ht' : t' ≤ n := by
              apply Nat.le_of_succ_le_succ
              simpa [Nat.succ_eq_add_one] using ht
            cases hstep : BB429OddExcursion.one z with
            | none =>
                simp [runNoFatal, hf, hstep] at hsafe
            | some d =>
                have htail : runNoFatal n d = some z' := by
                  simpa [runNoFatal, hf, hstep] using hsafe
                obtain ⟨p, hp, hpSafe⟩ := ih t' d z' htail ht'
                refine ⟨p, ?_, hpSafe⟩
                simp [BB429OddExcursion.run, hstep, hp]

/-- Guarded runs compose exactly, so separately certified source-safe
    segments can be joined without reopening their internal prefixes. -/
theorem runNoFatal_add (n k : Nat) (z : BB429OddExcursion.Zipper) :
    runNoFatal (n+k) z =
      (runNoFatal n z).bind (fun d => runNoFatal k d) := by
  induction n generalizing z with
  | zero =>
      simp [runNoFatal]
  | succ n ih =>
      simp only [Nat.succ_add, runNoFatal]
      by_cases hf : fatalCZero z
      · simp [hf]
      · simp only [hf, ite_false]
        rw [Option.bind_assoc]
        apply congrArg (fun f : BB429OddExcursion.Zipper → Option BB429OddExcursion.Zipper =>
          (BB429OddExcursion.one z).bind f)
        funext d
        exact ih d

/-- Endpoint form of guarded-run composition. -/
theorem runNoFatal_compose (n k : Nat) (z z' z'' : BB429OddExcursion.Zipper)
    (h₁ : runNoFatal n z = some z')
    (h₂ : runNoFatal k z' = some z'') :
    runNoFatal (n+k) z = some z'' := by
  rw [runNoFatal_add]
  simp [h₁, h₂]

#print axioms runNoFatal_to_run
#print axioms runNoFatal_prefix
#print axioms runNoFatal_add
#print axioms runNoFatal_compose

end BB429NoFatalGuard
