import BB429SourceE1Delta
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429W4HeadMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta

/-- Exact raw zipper execution, its final signed displacement, and the
maximum head displacement attained at any prefix, including the initial
position at displacement zero. This is a full-tape execution monitor. -/
def runWithMax : Nat → Zipper → Option (Zipper × Int × Int)
  | 0,c => some (c,0,0)
  | n+1,c => (oneWithDelta c).bind (fun p =>
      (runWithMax n p.1).map (fun q =>
        (q.1, p.2+q.2.1, max (0:Int) (p.2+q.2.2))))

private theorem runWithMax_nonneg (n : Nat) (c : Zipper) (p : Zipper × Int × Int)
    (hp : runWithMax n c = some p) : 0 ≤ p.2.2 := by
  cases n with
  | zero =>
      simp only [runWithMax, Option.some.injEq] at hp
      subst p
      simp
  | succ n =>
      simp only [runWithMax] at hp
      cases h : oneWithDelta c with
      | none => simp [h] at hp
      | some q =>
          simp only [h, Option.bind_some] at hp
          cases hn : runWithMax n q.1 with
          | none => simp [hn] at hp
          | some t =>
              simp only [hn, Option.map_some, Option.some.injEq] at hp
              have hp' : p = (t.1, q.2+t.2.1, max (0:Int) (q.2+t.2.2)) := by
                have heq : (t.1, q.2+t.2.1, max (0:Int) (q.2+t.2.2)) = p := by
                  simpa [h, hn] using hp
                exact heq.symm
              rw [hp']
              dsimp
              omega

/-- Exact associative composition of maximum head displacement. -/
theorem runWithMax_add (m n : Nat) (c : Zipper) :
  runWithMax (m+n) c =
    (runWithMax m c).bind (fun p =>
      (runWithMax n p.1).map (fun q =>
        (q.1,p.2.1+q.2.1,max p.2.2 (p.2.1+q.2.2)))) := by
  induction m generalizing c with
  | zero =>
      simp only [Nat.zero_add, runWithMax, Option.bind_some]
      cases hn : runWithMax n c with
      | none => simp [hn]
      | some q =>
          have hmax : max (0:Int) (0 + q.2.2) = q.2.2 := by
            have h := runWithMax_nonneg n c q hn
            omega
          cases q with
          | mk state tail =>
              cases tail with
              | mk d mx =>
                  simp only [Option.map_some, Option.some.injEq]
                  have h : (0:Int) ≤ mx := runWithMax_nonneg n c (state,d,mx) hn
                  simp [Int.max_def, h]
  | succ m ih =>
      simp only [Nat.succ_add, runWithMax]
      cases h : oneWithDelta c with
      | none => simp [h]
      | some p =>
          simp only [h, Option.bind_some]
          rw [ih]
          cases hm : runWithMax m p.1 with
          | none => simp [hm]
          | some a =>
              simp only [hm, Option.bind_some]
              cases hn : runWithMax n a.1 with
              | none => simp [hn]
              | some b =>
                  simp only [hn, Option.bind_some, Option.map_some,
                    Option.some.injEq, Prod.mk.injEq]
                  constructor
                  · trivial
                  · constructor
                    · omega
                    · omega

/-- The six-step E/F/C macro advances no farther right than its head
at entry while moving net four cells to the left. -/
theorem six_step_macro_max (tail suffix : List Bool) :
    runWithMax 6 (z 4 (leftBlock ++ tail) false (true :: suffix)) =
      some (z 4 tail false (true :: rightBlock ++ suffix), -4, 0) := by rfl

/-- The eight-step return macro moves four cells right and never beyond
that final position. -/
theorem eight_step_macro_max (left suffix : List Bool) :
    runWithMax 8 (z 2 left true (rightBlock ++ suffix)) =
      some (z 2 (ones 4 ++ left) true suffix, 4, 4) := by rfl

/-- Forty-one-step exceptional base, decomposed into short kernel-normalized
chunks to avoid exponential unfolding of the maximum expression. -/
theorem e1_base0_max (suffix : List Bool) :
    runWithMax (crossTime 0) (e1After 0 suffix) =
      some (z 2 (finalLeft 0) true suffix, 1, 1) := by
  have h0 : runWithMax 7 (e1After 0 suffix) =
    some ((z 1 [true] false ([true,true,true,true,true,true] ++ suffix)), -5, 0) := by rfl
  have h1 : runWithMax 7 (z 1 [true] false ([true,true,true,true,true,true] ++ suffix)) =
    some ((z 0 [true,true,true,true] false ([true,true,true] ++ suffix)), 3, 3) := by rfl
  have h2 : runWithMax 7 (z 0 [true,true,true,true] false ([true,true,true] ++ suffix)) =
    some ((z 5 [true] true ([false,true,false,true,false,true] ++ suffix)), -3, 2) := by rfl
  have h3 : runWithMax 7 (z 5 [true] true ([false,true,false,true,false,true] ++ suffix)) =
    some ((z 1 [true] false ([true,true,true,false,true,false,true,false,true] ++ suffix)), -3, 0) := by rfl
  have h4 : runWithMax 7 (z 1 [true] false ([true,true,true,false,true,false,true,false,true] ++ suffix)) =
    some ((z 0 [true,true,true,true] false ([false,true,false,true,false,true] ++ suffix)), 3, 3) := by rfl
  have h5 : runWithMax 6 (z 0 [true,true,true,true] false ([false,true,false,true,false,true] ++ suffix)) =
    some ((z 2 [true,false,true,false,true,true,true,true,true,true] true ([] ++ suffix)), 6, 6) := by rfl
  rw [show crossTime 0 = 7 + (7 + (7 + (7 + (7 + (6))))) by rfl, runWithMax_add, h0]
  simp only [Option.bind_some]
  rw [runWithMax_add, h1]
  simp only [Option.bind_some]
  rw [runWithMax_add, h2]
  simp only [Option.bind_some]
  rw [runWithMax_add, h3]
  simp only [Option.bind_some]
  rw [runWithMax_add, h4]
  simp only [Option.bind_some]
  rw [h5]
  rfl

/-- Fifteen-step exceptional base with one symbolic 01 pair. -/
theorem e1_base1_max (suffix : List Bool) :
    runWithMax (crossTime 1) (e1After 1 suffix) =
      some (z 2 (finalLeft 1) true suffix, 1, 1) := by
  have h0 : runWithMax 7 (e1After 1 suffix) =
    some ((z 0 [] false ([true,false,true,false,true,false,false,true] ++ suffix)), -7, 0) := by rfl
  have h1 : runWithMax 7 (z 0 [] false ([true,false,true,false,true,false,false,true] ++ suffix)) =
    some ((z 1 [true,true,true,true,true,true,true] false ([true] ++ suffix)), 7, 7) := by rfl
  have h2 : runWithMax 1 (z 1 [true,true,true,true,true,true,true] false ([true] ++ suffix)) =
    some ((z 2 [true,true,true,true,true,true,true,true] true ([] ++ suffix)), 1, 1) := by rfl
  rw [show crossTime 1 = 7 + (7 + (1)) by rfl, runWithMax_add, h0]
  simp only [Option.bind_some]
  rw [runWithMax_add, h1]
  simp only [Option.bind_some]
  rw [h2]
  rfl

/-- For every number of alternating pairs, the E/1 return reaches the
same scanned coordinate plus one from the post-instruction state, with
maximum displacement exactly +1. The arbitrary right suffix is untouched. -/
theorem e1_cross_max (b : Nat) (suffix : List Bool) :
    runWithMax (crossTime b) (e1After b suffix) =
      some (z 2 (finalLeft b) true suffix, 1, 1) := by
  have all : ∀ n, ∀ suffix,
      runWithMax (crossTime n) (e1After n suffix) =
      some (z 2 (finalLeft n) true suffix, 1, 1) := by
    apply nat_two_step_induction
    · intro suffix; exact e1_base0_max suffix
    · intro suffix; exact e1_base1_max suffix
    · intro n ih suffix
      have h6 : runWithMax 6 (e1After (n+2) suffix) =
          some (e1After n (rightBlock ++ suffix), -4, 0) := by
        cases n with
        | zero => rfl
        | succ n =>
          change runWithMax 6 (z 4 (leftBlock ++ (true :: (pairs01 n ++ ones 5))) false (true :: suffix)) =
            some (z 4 (true :: (pairs01 n ++ ones 5)) false (true :: rightBlock ++ suffix), -4, 0)
          exact six_step_macro_max (true :: (pairs01 n ++ ones 5)) suffix
      have h8 : runWithMax 8 (z 2 (finalLeft n) true (rightBlock ++ suffix)) =
          some (z 2 (ones 4 ++ finalLeft n) true suffix, 4, 4) := by
        exact eight_step_macro_max (finalLeft n) suffix
      have htime : crossTime (n+2) = 6 + (crossTime n + 8) := by
        simp [crossTime]; omega
      rw [htime, runWithMax_add, h6]
      simp only [Option.bind_some]
      rw [runWithMax_add, ih]
      simp only [Option.bind_some]
      rw [h8]
      simp [finalLeft, List.append_assoc, Int.max_def]
  exact all b suffix

/-- A source S_E scan returns to C/1 at exactly the same coordinate.
For every intermediate primitive step its head is at most that coordinate:
the exact maximum relative head displacement is zero. -/
theorem sourceScanE_e1_max (b : Nat) (suffix : List Bool) :
    runWithMax (crossTime b + 1) (sourceScanE b suffix) =
      some (z 2 (finalLeft b) true suffix, 0, 0) := by
  have hfirst : runWithMax 1 (sourceScanE b suffix) =
      some (e1After b suffix, -1, 0) := by
    cases b <;> rfl
  rw [show crossTime b + 1 = 1 + crossTime b by omega, runWithMax_add, hfirst]
  simp only [Option.bind_some]
  rw [e1_cross_max]
  rfl

#print axioms runWithMax_add
#print axioms e1_cross_max
#print axioms sourceScanE_e1_max

end BB429W4HeadMax
