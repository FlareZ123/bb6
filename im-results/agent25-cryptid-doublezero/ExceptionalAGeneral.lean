import Lean.Elab.Tactic.Omega
import ExceptionalARejoin
import ExceptionalBGeneral

set_option maxHeartbeats 5000000
namespace BB6.Agent25AGeneral
open CryptidBoundary BB6.BoundaryPadding

def K (t : Nat) : Nat := 8*t+6
def words (p : Nat) : List Bool := List.replicate (2*(p+1)) true
def ys : List Bool := List.replicate 6 true
def aCost (t p : Nat) : Nat :=
  (12*(K t)*(K t)+41*(K t)+32) +
    (CryptidA.wordCost (4*(K t)+3) (words p) +
      (2*(4*(K t)+3+CryptidA.wordInc (words p))+6))

private theorem code_repeat (n : Nat) :
    CryptidA.wordCode (List.replicate n true) = List.replicate (3*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, CryptidA.wordCode, ih]
    calc
      [true,true,true] ++ List.replicate (3*n) true =
         List.replicate 3 true ++ List.replicate (3*n) true := by rfl
      _ = List.replicate (3 + 3*n) true := List.replicate_append_replicate
      _ = List.replicate (3*(n+1)) true := by congr 1; omega

private theorem inc_repeat (n : Nat) :
    CryptidA.wordInc (List.replicate n true) = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [List.replicate_succ, CryptidA.wordInc, ih] using
      (show 4+4*n = 4*(n+1) by omega)

private theorem word_shape (p : Nat) :
    CryptidA.wordCode (words p) = List.replicate (6*(p+1)) true := by
  simp only [words,code_repeat]
  congr 1
  omega

private theorem word_inc (p : Nat) :
    CryptidA.wordInc (words p) = 8*(p+1) := by
  simp only [words,inc_repeat]
  omega

