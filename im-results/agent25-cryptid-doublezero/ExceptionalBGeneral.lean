import Lean.Elab.Tactic.Omega
import ExceptionalBRejoin

set_option maxHeartbeats 5000000
namespace BB6.Agent25BGeneral
open CryptidBoundary BB6.BoundaryPadding

def K (t : Nat) : Nat := 8*t+1
def bCost (t : Nat) : Nat := 12*(K t)*(K t)+49*(K t)+40

theorem oppairs_last (n : Nat) :
    oppairs (n+1) ++ [true] = false :: (pairs n ++ [true,true]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change false :: true :: (oppairs (n+1) ++ [true]) =
      false :: true :: false :: (pairs n ++ [true,true])
    rw [ih]

theorem output_input (t p : Nat) :
    BB6.Agent32EAll.output (3*t) (p+1) [] =
      init (List.replicate (3*(K t)) true ++
        false :: (List.replicate (2*p+4) true ++
          (false :: List.replicate 6 true))) := by
  have h : 8*(3*t)+5 = 2+3*(K t) := by unfold K; omega
  have hr : List.replicate (8*(3*t)+5) true =
      true :: true :: List.replicate (3*(K t)) true := by
    rw [h]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(K t)) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [BB6.Agent32EAll.output, List.append_nil]
  rw [hr]
  have hn : 2*(p+1)+2 = 2*p+4 := by omega
  rw [hn]
  simp [init, List.append_assoc]

