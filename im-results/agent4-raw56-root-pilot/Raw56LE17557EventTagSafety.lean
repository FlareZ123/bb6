import Raw56LE17557EventSubstitution

/-!
  Global terminal-run-tag *syntactic* safety of the abstract Raw56 17557
  parameterized event substitution.

  The state h is the number of finite right-hand one-runs beyond two.
  A decreases h by 1 and may only execute when h>=1; B increases h by 1.
  The boolean `last` is checked at each event: A is final iff h=1, while
  B is final iff h=0. Bad tags or underflow cause `none`.

  Every parameterized three-event expansion implements EXACTLY the same
  tag scan as its source event, for every initial h (even invalid ones).
  Consequently the recursively generated epochs are all tag-safe from
  initial h=1, and every epoch ends with h=1. This is an all-rank theorem
  about the abstract event grammar, not the original machine's all-time
  physical orbit. Source-level zipper/zero-run safety remains open.
-/

namespace BB6.Agent4Raw56LE17557EventTagSafety
open BB6.Agent4Raw56LE17557TimeCocycle
open BB6.Agent4Raw56LE17557EventSubstitution

def tagA (last : Bool) : Nat → Option Nat
  | 0 => none
  | h+1 => if last == (h == 0) then some h else none

def tagB (last : Bool) (h : Nat) : Option Nat :=
  if last == (h == 0) then some (h+1) else none

def stepTag : Triad → Nat → Option Nat
  | .aNormal _ _ _ last, h => tagA last h
  | .aCarry _ _ _ last, h => tagA last h
  | .b _ _ last, h => tagB last h

def runTag : List Triad → Nat → Option Nat
  | [], h => some h
  | e::es, h => (stepTag e h).bind (runTag es)

theorem runTag_append (xs ys : List Triad) (h : Nat) :
    runTag (xs ++ ys) h = (runTag xs h).bind (runTag ys) := by
  induction xs generalizing h with
  | nil => rfl
  | cons e es ih =>
      simp only [List.cons_append, runTag]
      cases hs : stepTag e h with
      | none => simp [hs]
      | some h' => simp [hs, ih]

/-- Every A-normal lifted three-event word has the same terminal-run
    safety and net height as one original A-normal event. -/
theorem expand_A_tag (a b c : Nat) (last : Bool) (h : Nat) :
    runTag (expand (.aNormal a b c last)) h =
      stepTag (.aNormal a b c last) h := by
  cases h with
  | zero => simp [expand, runTag, stepTag, tagA, tagB]
  | succ h =>
      cases h with
      | zero =>
          cases last <;> simp [expand, runTag, stepTag, tagA, tagB]
      | succ h =>
          cases last <;> simp [expand, runTag, stepTag, tagA, tagB]

theorem expand_C_tag (a c d : Nat) (last : Bool) (h : Nat) :
    runTag (expand (.aCarry a c d last)) h =
      stepTag (.aCarry a c d last) h := by
  cases h with
  | zero => simp [expand, runTag, stepTag, tagA, tagB]
  | succ h =>
      cases h with
      | zero =>
          cases last <;> simp [expand, runTag, stepTag, tagA, tagB]
      | succ h =>
          cases last <;> simp [expand, runTag, stepTag, tagA, tagB]

theorem expand_B_tag (a b : Nat) (last : Bool) (h : Nat) :
    runTag (expand (.b a b last)) h =
      stepTag (.b a b last) h := by
  cases h with
  | zero =>
      cases last <;> simp [expand, runTag, stepTag, tagA, tagB]
  | succ h =>
      cases last <;> simp [expand, runTag, stepTag, tagA, tagB]

theorem expand_tag (e : Triad) (h : Nat) :
    runTag (expand e) h = stepTag e h := by
  cases e with
  | aNormal a b c last => exact expand_A_tag a b c last h
  | aCarry a c d last => exact expand_C_tag a c d last h
  | b a b last => exact expand_B_tag a b last h

/-- Arbitrarily long words have exactly the same terminal-tag execution
    after full ABA/BBA expansion. -/
theorem expandWord_tag (xs : List Triad) (h : Nat) :
    runTag (expandWord xs) h = runTag xs h := by
  induction xs generalizing h with
  | nil => rfl
  | cons e es ih =>
      change runTag (expand e ++ expandWord es) h =
        (stepTag e h).bind (runTag es)
      rw [runTag_append, expand_tag]
      cases hs : stepTag e h with
      | none => simp [hs]
      | some h' => simp [hs, ih]

theorem base_tag : runTag baseEvents 1 = some 1 := by decide

/-- Exactly the missing pointwise tag consistency of every generated
    abstract epoch, including all terminal flags, at all ranks. -/
theorem epoch_tag_safe (n : Nat) :
    runTag (epochs n) 1 = some 1 := by
  induction n with
  | zero => exact base_tag
  | succ n ih =>
      change runTag (expandWord (epochs n)) 1 = some 1
      rw [expandWord_tag]
      exact ih

#print axioms expand_A_tag
#print axioms expand_B_tag
#print axioms expandWord_tag
#print axioms epoch_tag_safe

end BB6.Agent4Raw56LE17557EventTagSafety
