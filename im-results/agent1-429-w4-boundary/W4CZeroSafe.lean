import BB429SourceE1Return
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W4CZeroSafe

open BB429OddExcursion BB429SourceE1Return

/-- The exact original single-step interpreter, guarded against entering
    an instruction from a C/0 configuration. Its successful execution
    therefore certifies the absence of such configurations at every
    processed primitive step. -/
def oneSafe (c : Zipper) : Option Zipper :=
    if c.state == 2 && !c.current then none else one c

def runSafe : Nat → Zipper → Option Zipper
 | 0,c => some c
 | n+1,c => (oneSafe c).bind (runSafe n)

theorem runSafe_add (m n : Nat) (c : Zipper) :
    runSafe (m+n) c = (runSafe m c).bind (runSafe n) := by
  induction m generalizing c with
  | zero => simp [runSafe]
  | succ m ih =>
      simp only [Nat.succ_add, runSafe]
      cases h : oneSafe c with
      | none => simp
      | some d => simpa [h] using ih d

theorem six_safe (tail suffix : List Bool) :
    runSafe 6 (z 4 (leftBlock ++ tail) false (true :: suffix)) =
      some (z 4 tail false (true :: rightBlock ++ suffix)) := by rfl

theorem eight_safe (left suffix : List Bool) :
    runSafe 8 (z 2 left true (rightBlock ++ suffix)) =
      some (z 2 (ones 4 ++ left) true suffix) := by rfl

theorem e1base0 (suffix : List Bool) :
    runSafe (crossTime 0) (e1After 0 suffix) =
      some (z 2 (finalLeft 0) true suffix) := by rfl

theorem e1base1 (suffix : List Bool) :
    runSafe (crossTime 1) (e1After 1 suffix) =
      some (z 2 (finalLeft 1) true suffix) := by rfl

/-- No C/0 instruction occurs on the unbounded E/1 crossing. The proof
    uses the two source bases and a six/recursive/eight step induction. -/
theorem e1_cross_safe (b : Nat) (suffix : List Bool) :
    runSafe (crossTime b) (e1After b suffix) =
      some (z 2 (finalLeft b) true suffix) := by
  have all : ∀ n, ∀ suffix,
      runSafe (crossTime n) (e1After n suffix) =
        some (z 2 (finalLeft n) true suffix) := by
    apply nat_two_step_induction
    · intro suffix; exact e1base0 suffix
    · intro suffix; exact e1base1 suffix
    · intro n ih suffix
      have h6 : runSafe 6 (e1After (n+2) suffix) =
          some (e1After n (rightBlock ++ suffix)) := by
        cases n with
        | zero => rfl
        | succ n =>
          change runSafe 6
              (z 4 (leftBlock ++ (true :: (pairs01 n ++ ones 5))) false
                (true :: suffix)) =
            some (z 4 (true :: (pairs01 n ++ ones 5)) false
              (true :: rightBlock ++ suffix))
          exact six_safe (true :: (pairs01 n ++ ones 5)) suffix
      have h8 : runSafe 8
          (z 2 (finalLeft n) true (rightBlock ++ suffix)) =
          some (z 2 (ones 4 ++ finalLeft n) true suffix) := by
        exact eight_safe (finalLeft n) suffix
      have htime : crossTime (n+2) = 6 + (crossTime n + 8) := by
        simp [crossTime]; omega
      rw [htime, runSafe_add, h6]
      simp only [Option.bind_some]
      rw [runSafe_add, ih]
      simp only [Option.bind_some]
      simpa [finalLeft, List.append_assoc] using h8
  exact all b suffix

/-- Source S_E, with any alternating-pair parameter and any right suffix,
    returns to C/1 without making a single C/0 transition. -/
theorem scanE_safe (b : Nat) (suffix : List Bool) :
    runSafe (crossTime b + 1) (sourceScanE b suffix) =
      some (z 2 (finalLeft b) true suffix) := by
  have h1 : runSafe 1 (sourceScanE b suffix) =
      some (e1After b suffix) := by
    cases b <;> rfl
  rw [show crossTime b+1 = 1+crossTime b by omega,
    runSafe_add, h1]
  simp only [Option.bind_some]
  exact e1_cross_safe b suffix

theorem runSafe_to_run (n : Nat) (c d : Zipper)
    (h : runSafe n c = some d) : run n c = some d := by
  induction n generalizing c with
  | zero => simpa [runSafe, run] using h
  | succ n ih =>
      simp only [runSafe] at h
      cases hs : oneSafe c with
      | none => simp [hs] at h
      | some p =>
          simp only [hs, Option.bind_some] at h
          have hone : one c = some p := by
            unfold oneSafe at hs
            split at hs
            · simp at hs
            · exact hs
          simp only [run, hone, Option.bind_some]
          exact ih p h

theorem runSafe_prefix (m n : Nat) (c d : Zipper)
    (h : runSafe (m+n) c = some d) :
    ∃ p, runSafe m c = some p ∧ runSafe n p = some d := by
  rw [runSafe_add] at h
  cases hm : runSafe m c with
  | none => simp [hm] at h
  | some p =>
      refine ⟨p, rfl, ?_⟩
      simpa [hm] using h

theorem runSafe_no_czero_prefix (n t : Nat) (c d : Zipper)
    (h : runSafe n c = some d) (ht : t < n) :
    ∃ p, run t c = some p ∧
      (p.state == 2 && !p.current) = false := by
  have htime : n = t + (n-(t+1)+1) := by omega
  rw [htime] at h
  obtain ⟨p, hpre, hsuf⟩ :=
    runSafe_prefix t (n-(t+1)+1) c d h
  have hgood : (p.state == 2 && !p.current) = false := by
    cases hbad : (p.state == 2 && !p.current) with
    | false => rfl
    | true => simp [runSafe, oneSafe, hbad] at hsuf
  exact ⟨p, runSafe_to_run t c p hpre, hgood⟩

/-- A direct all-prefix statement for the original BB429 raw zipper.
    Every time t through the C/1 return has a defined source run
    at a non-C/0 configuration. This also covers the endpoint. -/
theorem scanE_no_czero_any_prefix (b t : Nat) (suffix : List Bool)
    (ht : t ≤ crossTime b + 1) :
    ∃ p, run t (sourceScanE b suffix) = some p ∧
      (p.state == 2 && !p.current) = false := by
  by_cases hlt : t < crossTime b+1
  · exact runSafe_no_czero_prefix (crossTime b+1) t
       (sourceScanE b suffix) (z 2 (finalLeft b) true suffix)
       (scanE_safe b suffix) hlt
  · have heq : t = crossTime b + 1 := by omega
    subst t
    exact ⟨z 2 (finalLeft b) true suffix,
      runSafe_to_run (crossTime b+1) (sourceScanE b suffix)
        (z 2 (finalLeft b) true suffix)
        (scanE_safe b suffix), by rfl⟩

#print axioms e1_cross_safe
#print axioms scanE_safe
#print axioms runSafe_to_run
#print axioms scanE_no_czero_any_prefix

end BB429W4CZeroSafe
