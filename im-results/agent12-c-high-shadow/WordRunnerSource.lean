import WordRunner
import WordBlockSource
import ClosedBounce
import GenericSection

namespace BB6.Agent12WordRunner
open BB6.Agent12WordBlock BB6.Agent46

def fastNext (p : Pair) : Option Pair :=
  (BB6.Agent12ClosedBounce.closedSection p).2

theorem fastNext_eq (p : Pair) : fastNext p=secNext p := by
  simpa only [fastNext,secNext] using congrArg Prod.snd (BB6.Agent12ClosedBounce.closedSection_eq p)

theorem fastLaw : EdgeLaw fastNext := by
  rw [show fastNext=secNext from funext fastNext_eq]
  exact source_edge_law

theorem runNext_eq_source (n : Nat) (s : Option Pair) :
    runNext secNext n s=BB6.Agent8Section.run secNext n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simpa only [runNext,BB6.Agent8Section.run_succ_head] using ih (s.bind secNext)

def fastRun (bits n : Nat) (p : Pair) : Option Pair :=
  let tab := makeTable bits
  runBudget fastNext fastLaw (tablePredict bits tab) n p

theorem fastRun_eq (bits n : Nat) (p : Pair) :
    fastRun bits n p=BB6.Agent8Section.run secNext n (some p) := by
  unfold fastRun
  rw [runBudget_eq,show fastNext=secNext from funext fastNext_eq]
  exact runNext_eq_source n (some p)

#print axioms fastRun_eq
end BB6.Agent12WordRunner
