import Raw56LE17557ActionGrammar

namespace BB6.Agent1Raw56.LE17557FrameMachine
open BB6.Agent1Raw56.LE17557FrameSchedule
open BB6.Agent1Raw56.LE17557ActionGrammar

def hitAction : Bool → Action
  | true => .b
  | false => .carry

def hitWord (w : List Bool) : List Action := w.map hitAction

/-- Abstract finite-zero-run stack semantics of the rank-labelled action
    grammar.  A normal action pushes the exact low-side cost of its frame.
    B/carry consume seven/one cells and pop a frame exactly at exhaustion. -/
def stepLow : Action → List Nat → Option (List Nat)
  | .normal r, st => some (lowCost (frame r) :: st)
  | .b, [] => none
  | .b, z :: zs =>
      if z < 7 then none else if z = 7 then some zs else some ((z-7) :: zs)
  | .carry, [] => none
  | .carry, z :: zs =>
      if z < 1 then none else if z = 1 then some zs else some ((z-1) :: zs)

def execLow : List Action → List Nat → Option (List Nat)
  | [], st => some st
  | a :: as, st => (stepLow a st).bind (execLow as)

theorem execLow_append (u v : List Action) (st : List Nat) :
    execLow (u ++ v) st = (execLow u st).bind (execLow v) := by
  induction u generalizing st with
  | nil => rfl
  | cons a u ih =>
      simp only [List.cons_append, execLow]
      cases h : stepLow a st with
      | none => simp [h]
      | some st' => simp [h, ih]

@[simp] theorem hitWord_append (u v : List Bool) :
    hitWord (u ++ v) = hitWord u ++ hitWord v := by
  simp [hitWord]

theorem lowCost_cons_pos (a : Bool) (w : List Bool) :
    1 ≤ lowCost (a :: w) := by
  cases a <;> simp [lowCost, countB, countC] <;> omega

/-- A nonempty hit word consumes exactly its own low-side cost and pops the
    frame.  No special property of the recursive frame word is needed here:
    positivity of every B/C action cost is enough. -/
theorem hitWord_consumes_own_cost (a : Bool) (w : List Bool) (st : List Nat) :
    execLow (hitWord (a :: w)) (lowCost (a :: w) :: st) = some st := by
  induction w generalizing a st with
  | nil =>
      cases a <;> simp [hitWord, execLow, stepLow, lowCost, countB, countC]
  | cons b w ih =>
      have hp : 1 ≤ lowCost (b :: w) := lowCost_cons_pos b w
      cases a <;>
        simp only [hitWord, List.map_cons, execLow] <;>
        simp [stepLow, lowCost, countB, countC] at hp ⊢ <;>
        split <;> try omega
      · simpa [hitWord] using ih b st
      · simpa [hitWord] using ih b st

theorem frame_nonempty (r : Nat) : frame r ≠ [] := by
  cases r <;> simp [frame]

/-- A bounded outer trace can be executed by replacing each complete nested
    segment with the induction hypothesis that it closes, leaving only the
    advertised B/C hit word on the current outer frame. -/
theorem outerTraceBelow_exec {k : Nat} {xs : List Action} {hs : List Bool}
    (h : OuterTraceBelow k xs hs)
    (closed : ∀ {r : Nat}, r < k → ∀ st, execLow (segment r) st = some st)
    (st : List Nat) :
    execLow xs st = execLow (hitWord hs) st := by
  induction h generalizing st with
  | nil => rfl
  | hitB h ih =>
      simp only [execLow, hitWord, List.map_cons, hitAction]
      cases hb : stepLow .b st with
      | none => simp [hb]
      | some st' => simpa [hb] using ih st'
  | hitC h ih =>
      simp only [execLow, hitWord, List.map_cons, hitAction]
      cases hc : stepLow .carry st with
      | none => simp [hc]
      | some st' => simpa [hc] using ih st'
  | @skip r hr xs hs h ih =>
      rw [execLow_append, closed hr st]
      simp
      exact ih st

/-- Main well-founded frame theorem: every rank-labelled segment is a complete
    finite frame.  It pushes one finite zero-run, safely executes all nested
    lower-rank frames and its exact outer F_r hit schedule, then pops itself,
    restoring the incoming stack verbatim. -/
theorem segment_closes_low (r : Nat) (st : List Nat) :
    execLow (segment r) st = some st := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      rw [segment_eq_normal_body]
      simp only [execLow, stepLow, Option.bind_some]
      have ht := outerTraceBelow_exec (body_outerTraceBelow r)
        (closed := by
          intro q hq st'
          exact ih q hq st')
        (lowCost (frame r) :: st)
      rw [ht]
      have hn := frame_nonempty r
      cases hf : frame r with
      | nil => exact False.elim (hn hf)
      | cons a w =>
          simpa [hf] using hitWord_consumes_own_cost a w st

/-- The normal-A rank formula agrees exactly with the abstract frame-stack
    push size used above. -/
theorem normal_push_eq_frame_cost (r : Nat) :
    normalB r - 6 = lowCost (frame r) := by
  rw [frame_lowCost]
  unfold normalB
  have hp := pow_ge16 r
  simp [Nat.pow_succ]
  omega

/-- Root-level B/C hits in epoch n after all complete nested finite frames
    are hidden.  Epoch zero here is the physical C_2 -> C_3 epoch. -/
def rootHits : Nat → List Bool
  | 0 => [false, true, true, false]
  | n+1 => refine (rootHits n)

theorem actionEpoch_rootTraceBelow (n : Nat) :
    OuterTraceBelow n (actionEpoch n) (rootHits n) := by
  induction n with
  | zero =>
      exact OuterTraceBelow.hitC
        (OuterTraceBelow.hitB
          (OuterTraceBelow.hitB
            (OuterTraceBelow.hitC OuterTraceBelow.nil)))
  | succ n ih =>
      simpa [actionEpoch, rootHits] using outerTraceBelow_lift ih

theorem countB_refine (w : List Bool) :
    countB (refine w) = 2 * countB w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [refine_cons, countB_append, ih]
      cases a <;> simp [refineLetter, countB] <;> omega

theorem countC_refine (w : List Bool) :
    countC (refine w) = countB w + countC w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [refine_cons, countC_append, ih]
      cases a <;> simp [refineLetter, countB, countC] <;> omega

theorem rootHits_counts (n : Nat) :
    countB (rootHits n) = 2^(n+1) ∧
    countC (rootHits n) = 2^(n+1) := by
  induction n with
  | zero => decide
  | succ n ih =>
      rcases ih with ⟨hb,hc⟩
      rw [rootHits, countB_refine, countC_refine, hb, hc]
      simp [Nat.pow_succ]
      omega

/-- Exact root blank displacement of the physical epoch C_(n+2) -> C_(n+3). -/
theorem rootHits_lowCost (n : Nat) :
    lowCost (rootHits n) = 2^(n+4) := by
  rcases rootHits_counts n with ⟨hb,hc⟩
  unfold lowCost
  rw [hb,hc]
  simp [Nat.pow_succ]
  omega

theorem rootHits_nonempty (n : Nat) : rootHits n ≠ [] := by
  intro h
  have hc := (rootHits_counts n).1
  rw [h] at hc
  simp [countB] at hc
  have hp : 0 < 2^(n+1) := Nat.pow_pos (by omega)
  omega

/-- The complete rank-labelled epoch is stack-safe against a root runway whose
    size is exactly the checkpoint displacement.  Every nested finite frame
    closes by strict-rank induction, leaving precisely the root hit word. -/
theorem actionEpoch_consumes_root (n : Nat) (st : List Nat) :
    execLow (actionEpoch n) (2^(n+4) :: st) = some st := by
  rw [← rootHits_lowCost n]
  have ht := outerTraceBelow_exec (actionEpoch_rootTraceBelow n)
    (closed := by
      intro r hr st'
      exact segment_closes_low r st')
    (lowCost (rootHits n) :: st)
  rw [ht]
  have hn := rootHits_nonempty n
  cases hroot : rootHits n with
  | nil => exact False.elim (hn hroot)
  | cons a w =>
      simpa [hroot] using hitWord_consumes_own_cost a w st

#print axioms actionEpoch_rootTraceBelow
#print axioms rootHits_counts
#print axioms rootHits_lowCost
#print axioms actionEpoch_consumes_root
#print axioms hitWord_consumes_own_cost
#print axioms outerTraceBelow_exec
#print axioms segment_closes_low
#print axioms normal_push_eq_frame_cost

end BB6.Agent1Raw56.LE17557FrameMachine
