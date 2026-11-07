import BB429SourceE1Return
import Lean.Elab.Tactic.Omega

namespace BB429SourceE1Delta
open BB429OddExcursion BB429SourceE1Return

/-- One raw zipper instruction, augmented with its signed head displacement. -/
def oneWithDelta (c : Zipper) : Option (Zipper × Int) :=
  match action c.state c.current with
  | none => none
  | some (_,_,rightward) =>
      (one c).map (fun c' => (c', if rightward then 1 else -1))

/-- Exact raw run together with the sum of its left/right head movements. -/
def runWithDelta : Nat → Zipper → Option (Zipper × Int)
 | 0,c => some (c,0)
 | n+1,c =>
    (oneWithDelta c).bind (fun p =>
      (runWithDelta n p.1).map (fun q => (q.1,p.2+q.2)))

theorem runWithDelta_add (m n : Nat) (c : Zipper) :
  runWithDelta (m+n) c =
    (runWithDelta m c).bind (fun p =>
      (runWithDelta n p.1).map (fun q => (q.1,p.2+q.2))) := by
  induction m generalizing c with
  | zero => simp [runWithDelta]
  | succ m ih =>
    simp only [Nat.succ_add, runWithDelta]
    rw [Option.bind_assoc]
    congr 1
    funext p
    rw [ih p.1]
    cases hm : runWithDelta m p.1 with
    | none => simp [hm]
    | some q =>
      cases hn : runWithDelta n q.1 with
      | none => simp [hm,hn]
      | some r => simp [hm,hn,Int.add_assoc]

theorem six_step_macro_delta (tail suffix : List Bool) :
  runWithDelta 6 (z 4 (leftBlock ++ tail) false (true :: suffix)) =
    some (z 4 tail false (true :: rightBlock ++ suffix), -4) := by
  rfl

theorem eight_step_macro_delta (left suffix : List Bool) :
  runWithDelta 8 (z 2 left true (rightBlock ++ suffix)) =
    some (z 2 (ones 4 ++ left) true suffix, 4) := by
  rfl

/-- The same two-step induction as e1_cross, now tracking the exact signed
    displacement of the head. The post-E/1 head ends one cell to the right. -/
theorem e1_cross_delta (b : Nat) (suffix : List Bool) :
  runWithDelta (crossTime b) (e1After b suffix) =
    some (z 2 (finalLeft b) true suffix, 1) := by
  have hAll : ∀ n, ∀ suffix, runWithDelta (crossTime n) (e1After n suffix) =
      some (z 2 (finalLeft n) true suffix, 1) := by
    apply nat_two_step_induction
    · intro suffix; rfl
    · intro suffix; rfl
    · intro n ih suffix
      have h6 : runWithDelta 6 (e1After (n+2) suffix) =
          some (e1After n (rightBlock ++ suffix), -4) := by
        cases n with
        | zero => rfl
        | succ n =>
          change runWithDelta 6 (z 4 (leftBlock ++ (true :: (pairs01 n ++ ones 5))) false (true :: suffix)) =
            some (z 4 (true :: (pairs01 n ++ ones 5)) false (true :: rightBlock ++ suffix), -4)
          exact six_step_macro_delta (true :: (pairs01 n ++ ones 5)) suffix
      have hi := ih (rightBlock ++ suffix)
      have h8 : runWithDelta 8 (z 2 (finalLeft n) true (rightBlock ++ suffix)) =
          some (z 2 (ones 4 ++ finalLeft n) true suffix, 4) := by
        exact eight_step_macro_delta (finalLeft n) suffix
      have htime : crossTime (n+2) = 6 + (crossTime n + 8) := by
        simp [crossTime]
        omega
      rw [htime, runWithDelta_add, h6]
      simp only [Option.bind_some]
      rw [runWithDelta_add, hi]
      simp only [Option.bind_some]
      rw [h8]
      simp [finalLeft, Int.add_assoc]
  exact hAll b suffix

/-- The initial E/1 instruction moves left by one. -/
theorem sourceScanE_e1_step_delta (b : Nat) (suffix : List Bool) :
  oneWithDelta (sourceScanE b suffix) = some (e1After b suffix, -1) := by
  cases b <;> rfl

/-- Including the initial E/1 instruction, the head returns to its original
    coordinate: the total signed displacement is exactly zero. -/
theorem sourceScanE_e1_revisit_delta (b : Nat) (suffix : List Bool) :
  runWithDelta (crossTime b + 1) (sourceScanE b suffix) =
    some (z 2 (finalLeft b) true suffix, 0) := by
  have h1 : runWithDelta 1 (sourceScanE b suffix) =
      some (e1After b suffix, -1) := by
    simp [runWithDelta, sourceScanE_e1_step_delta]
  rw [show crossTime b + 1 = 1 + crossTime b by omega, runWithDelta_add, h1]
  simp only [Option.bind_some]
  rw [e1_cross_delta]
  simp

#print axioms e1_cross_delta
#print axioms sourceScanE_e1_revisit_delta

end BB429SourceE1Delta
