import FiniteHalting
import WeightedFirstOneCover
import SideCycle

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! A unified checker for genuine Raw34 source halters and oriented side cycles. -/
namespace BB6.Agent23Raw34Next
open BB6Coverage BB6.Agent13BlankDelay
open BB6Coverage.Agent50SideCycle

/-- Code 0=wildcard, 1=assigned HALT, 2..25=24 ordinary moves in
write/turn/next-state order. Source native `Transition`, not an external machine. -/
def moves : List Move :=
  [false,true].flatMap fun w =>
    [false,true].flatMap fun r =>
      (List.finRange 6).map fun q => ⟨w,r,q⟩

def table (codes : List Nat) : PartialMachine := fun s =>
  let code := (codes[2*s.1.val+s.2.toNat]?).getD 0
  if code = 0 then none
  else if code = 1 then some none
  else (moves[code-2]?).map some

inductive Cert where
  | halt (n : Nat)
  | side (entry period : Nat) (right : Bool) (boundary : Int)

structure Witness where
  codes : List Nat
  cert : Cert

def check (w : Witness) : Bool :=
  match w.cert with
  | .halt n => decide (n+1 ≤ 27) && finiteHaltCheck (table w.codes) n
  | .side entry period right boundary =>
      decide (0 < period) && fastSideCycleCheck (table w.codes)
        entry period right boundary

theorem check_sound (w : Witness) (h : check w = true) :
    ∀ m, compatible (table w.codes) m → WeightedBound 32 m := by
  cases w with
  | mk codes cert =>
    cases cert with
    | halt n =>
      have hh : decide (n+1 ≤ 27) = true ∧
          finiteHaltCheck (table codes) n = true := by
        simpa only [check, Bool.and_eq_true] using h
      intro m hm
      exact weighted_of_margin 32 m
        ((finiteHaltCheck_sound (table codes) n 27
          (of_decide_eq_true hh.1) hh.2).sound m hm)
        (by decide)
    | side entry period right boundary =>
      have hh : decide (0 < period) = true ∧
          fastSideCycleCheck (table codes) entry period right boundary = true := by
        simpa only [check, Bool.and_eq_true] using h
      intro m hm
      exact weighted_of_never 32 m
        (fastSideCycleCheck_sound (table codes)
          entry period right boundary (of_decide_eq_true hh.1)
          hh.2 m hm)

#print axioms check_sound
end BB6.Agent23Raw34Next
