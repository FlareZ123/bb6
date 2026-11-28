import Agent46CanonicalCut
import Raw44FastZipCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent16Raw44FastCanonical
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent46CanonicalCut BB6.Agent46StateClosure BB6.Agent16Raw44FastZip

def fast (B : Nat) (p : PartialMachine) (cut : Nat) : Cut → Bool
  | .unresolved => true
  | .closed t => fastCheck B p t
  | .bounded q C _ => tableOK p q && decide (C ≤ B)
  | .state mask => stateCheck p mask
  | .split n s kids => quickQuery B p n s &&
      allMoves (fun mv => if mv.next.val ≤ cut then
        fast B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true)
termination_by structural t => t

theorem fast_eq (B : Nat) (p : PartialMachine) (cut : Nat) (t : Cut) :
    fast B p cut t = check B p cut t := by
  induction t generalizing p cut with
  | unresolved => rfl
  | closed t => exact fastCheck_eq B p t
  | bounded q C safe => rfl
  | state mask => rfl
  | split n s kids ih =>
    simp only [fast,Agent46CanonicalCut.check,quickQuery_eq]
    have h : (fun mv => if mv.next.val ≤ cut then
          fast B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) =
        (fun mv => if mv.next.val ≤ cut then
          check B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) := by
      funext mv
      split <;> simp only [ih]
    rw [h]

theorem fast_sound {B : Nat} {p : PartialMachine} {cut : Nat} {t : Cut}
    (h : fast B p cut t = true) : check B p cut t = true := by
  simpa only [fast_eq] using h

theorem split_checked (B : Nat) (p : PartialMachine) (cut n : Nat) (s : Slot)
    (kids : Move → Cut) (query : quickQuery B p n s = true)
    (each : ∀ mv : Move, (if mv.next.val ≤ cut then
      check B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true) = true) :
    check B p cut (.split n s kids) = true := by
  change (zipQueryOK B p n s && allMoves (fun mv => if mv.next.val ≤ cut then
      check B (refine p s (some mv)) (nextCut cut mv) (kids mv) else true)) = true
  rw [← quickQuery_eq,query, Bool.true_and]
  exact allMoves_of _ each

#print axioms fast_eq
#print axioms fast_sound
#print axioms split_checked
end BB6.Agent16Raw44FastCanonical
