import Lean.Elab.Tactic.Omega
import EZeroZTwoFollow
import CodeImplicitNil
import ABridgeTwo

namespace BB6.Agent36EZeroZTwoA
open CryptidBoundary
open BB6.Agent36EZeroZTwoFollow

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

private theorem code_append (xs ys : List Bool) :
    CryptidA.wordCode (xs ++ ys) =
      CryptidA.wordCode xs ++ CryptidA.wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [CryptidA.wordCode, ih, List.append_assoc]

private theorem code_ones (n : Nat) :
    CryptidA.wordCode (List.replicate n true) =
      List.replicate (3*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, CryptidA.wordCode, ih]
    rw [show 3*(n+1)=3+3*n by omega,
      ←List.replicate_append_replicate]
    rfl

def aWords (s : Nat) : List Bool :=
  [true,false,false,false,false] ++ List.replicate (2*s) true

private theorem aWords_shape (s : Nat) :
    false :: CryptidA.wordCode (aWords s) =
      BB6.Agent32EZero.packetZero ++ List.replicate (6*s) true := by
  rw [show 6*s=3*(2*s) by omega,←code_ones]
  simp [aWords, code_append, CryptidA.wordCode,
    BB6.Agent32EZero.packetZero,List.append_assoc]

private theorem a_shape (t s : Nat) :
    postZ (3*t) (3*s) =
      init (List.replicate (3*(8*t)+1) true ++
        false::CryptidA.wordCode (aWords s)) := by
  have hn : List.replicate (8*(3*t)+3) true =
      true :: true :: List.replicate (3*(8*t)+1) true := by
    rw [show 8*(3*t)+3=2+(3*(8*t)+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp only [postZ,init,hn,List.cons_append]
  rw [aWords_shape]
  rw [show 2*(3*s)=6*s by omega]
  simp [List.append_assoc]

def aTime (t s : Nat) : Nat :=
   (12*(8*t)*(8*t)+41*(8*t)+32) +
     (CryptidA.wordCost (4*(8*t)+3) (aWords s) +
       (2*((4*(8*t)+3)+CryptidA.wordInc (aWords s))+6))

def aUnary (t s : Nat) : Nat :=
  2*((4*(8*t)+3)+CryptidA.wordInc (aWords s))+5

/-- k ≡ 0 and marker depth divisible by three: exactly two returns,
    ending with a fully unary right tape. -/
theorem a_follow_multiple_three (t s : Nat) :
    run (aTime t s) (postZ (3*t) (3*s)) =
      ⟨[],false,List.replicate (aUnary t s) true,5⟩ := by
  rw [a_shape]
  exact BB6.Agent32Code.full_A_code_implicit_nil (8*t) (aWords s)

theorem a_two_return_multiple_three (t s : Nat) :
    run (firstTime (3*t) (3*s)+aTime t s) (input (3*t) (3*s)) =
      ⟨[],false,List.replicate (aUnary t s) true,5⟩ := by
  have hfirst : run (firstTime (3*t) (3*s)) (input (3*t) (3*s)) =
      postZ (3*t) (3*s) := by
    simpa only [firstTime,input,postZ,List.append_nil,List.cons_append] using
      (BB6.Agent36EZeroZTwo.full_E_zero_pairs_all (3*t) (3*s) [])
  rw [run_add,hfirst]
  exact a_follow_multiple_three t s

#print axioms a_follow_multiple_three
#print axioms a_two_return_multiple_three
end BB6.Agent36EZeroZTwoA
