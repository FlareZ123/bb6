import Lean.Elab.Tactic.Omega
import EZeroZTwoFollow
import CodeImplicitNil
import ABridgeTwo
import BoundaryPadding

namespace BB6.Agent36EZeroZTwoA
open CryptidBoundary
open BB6.Agent36EZeroZTwoFollow
open BB6.BoundaryPadding BB6.Padding

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

private theorem a_shape_plus_one (t s : Nat) :
    postZ (3*t) (3*s+1) =
      init (List.replicate (3*(8*t)+1) true ++
        false::(CryptidA.wordCode (aWords s) ++ [true,true])) := by
  have hn : List.replicate (8*(3*t)+3) true =
      true :: true :: List.replicate (3*(8*t)+1) true := by
    rw [show 8*(3*t)+3=2+(3*(8*t)+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hs : List.replicate (2*(3*s+1)) true =
      List.replicate (6*s) true ++ [true,true] := by
    rw [show 2*(3*s+1)=6*s+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  simp only [postZ,init,hn,List.cons_append]
  have hw : BB6.Agent32EZero.packetZero ++
      (List.replicate (6*s) true ++ [true,true]) =
      false :: (CryptidA.wordCode (aWords s) ++ [true,true]) := by
    rw [←List.append_assoc,←aWords_shape]
    rfl
  rw [hs]
  rw [hw]
  simp [List.append_assoc]

private theorem a_shape_plus_two (t s : Nat) :
    postZ (3*t) (3*s+2) =
      init (List.replicate (3*(8*t)+1) true ++
        false::(CryptidA.wordCode (aWords s ++ [true]) ++ [true])) := by
  have hn : List.replicate (8*(3*t)+3) true =
      true :: true :: List.replicate (3*(8*t)+1) true := by
    rw [show 8*(3*t)+3=2+(3*(8*t)+1) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hs : List.replicate (2*(3*s+2)) true =
      List.replicate (6*s) true ++ [true,true,true,true] := by
    rw [show 2*(3*s+2)=6*s+4 by omega,
      ←List.replicate_append_replicate]
    rfl
  simp only [postZ,init,hn,List.cons_append]
  have hw : BB6.Agent32EZero.packetZero ++
      (List.replicate (6*s) true ++ [true,true,true,true]) =
      false :: (CryptidA.wordCode (aWords s ++ [true]) ++ [true]) := by
    rw [←List.append_assoc,←aWords_shape,code_append]
    simp [CryptidA.wordCode,List.append_assoc]
  rw [hs]
  rw [hw]
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

def aDoubleTime (t s : Nat) : Nat :=
  (12*(8*t)*(8*t)+41*(8*t)+32) +
    (CryptidA.wordCost (4*(8*t)+3) (aWords s) +
      (2*((4*(8*t)+3)+CryptidA.wordInc (aWords s))+16))

def aDoubleUnary (t s : Nat) : Nat :=
  2*((4*(8*t)+3)+CryptidA.wordInc (aWords s))+1

/-- Every marker length 3s+1 returns to regular 0 1^6 modulo
    a physically invisible double blank at the far tape end. -/
theorem a_follow_plus_one (t s : Nat) :
    ObsEq (run (aDoubleTime t s) (postZ (3*t) (3*s+1)))
      (⟨[],false,List.replicate (aDoubleUnary t s) true ++
        (false :: List.replicate 6 true),5⟩ : Cfg) := by
  let xs := List.replicate (3*(8*t)+1) true ++
    false :: (CryptidA.wordCode (aWords s) ++ [true,true])
  have hshape : postZ (3*t) (3*s+1) = init xs :=
    a_shape_plus_one t s
  have hpad := source_init_pad (aDoubleTime t s) 2 xs
  change ObsEq (run (aDoubleTime t s) (init xs))
      (run (aDoubleTime t s) (init (xs ++ List.replicate 2 false))) at hpad
  have hs : xs ++ List.replicate 2 false =
      List.replicate (3*(8*t)+1) true ++
        false :: (CryptidA.wordCode (aWords s) ++
          ([true,true,false,false] ++ [])) := by
    simp [xs,List.append_assoc]
  rw [←hshape,hs] at hpad
  have hraw := BB6.Agent35.full_A_code_double (8*t) (aWords s) []
  change run (aDoubleTime t s)
      (init (List.replicate (3*(8*t)+1) true ++
        false :: (CryptidA.wordCode (aWords s) ++
          ([true,true,false,false] ++ [])))) =
      (⟨[],false,List.replicate (aDoubleUnary t s) true ++
        (false :: List.replicate 6 true),5⟩ : Cfg) at hraw
  rw [hraw] at hpad
  exact hpad

def aExtraWord (s : Nat) : List Bool := aWords s ++ [true,false]

def aExtraTime (t s : Nat) : Nat :=
  (12*(8*t)*(8*t)+41*(8*t)+32) +
    (CryptidA.wordCost (4*(8*t)+3) (aExtraWord s) +
      (2*((4*(8*t)+3)+CryptidA.wordInc (aExtraWord s))+6))

def aExtraUnary (t s : Nat) : Nat :=
  2*((4*(8*t)+3)+CryptidA.wordInc (aExtraWord s))+5

/-- Every marker length 3s+2 returns to an entirely unary section
    modulo the single implicit blank consumed by the final 10 token. -/
theorem a_follow_plus_two (t s : Nat) :
    ObsEq (run (aExtraTime t s) (postZ (3*t) (3*s+2)))
      (⟨[],false,List.replicate (aExtraUnary t s) true,5⟩ : Cfg) := by
  let xs := List.replicate (3*(8*t)+1) true ++
    false :: (CryptidA.wordCode (aWords s ++ [true]) ++ [true])
  have hshape : postZ (3*t) (3*s+2) = init xs :=
    a_shape_plus_two t s
  have hpad := source_init_pad (aExtraTime t s) 1 xs
  change ObsEq (run (aExtraTime t s) (init xs))
      (run (aExtraTime t s) (init (xs ++ List.replicate 1 false))) at hpad
  have hs : xs ++ List.replicate 1 false =
      List.replicate (3*(8*t)+1) true ++
        false :: CryptidA.wordCode (aExtraWord s) := by
    simp [xs,aExtraWord,code_append,CryptidA.wordCode,List.append_assoc]
  rw [←hshape,hs] at hpad
  have hraw := BB6.Agent32Code.full_A_code_implicit_nil (8*t) (aExtraWord s)
  change run (aExtraTime t s)
      (init (List.replicate (3*(8*t)+1) true ++
        false :: CryptidA.wordCode (aExtraWord s))) =
      (⟨[],false,List.replicate (aExtraUnary t s) true,5⟩ : Cfg) at hraw
  rw [hraw] at hpad
  exact hpad

/-- The exceptional A code remains complete after composing the E first return. -/
theorem a_two_return_plus_one (t s : Nat) :
    ObsEq (run (firstTime (3*t) (3*s+1)+aDoubleTime t s)
      (input (3*t) (3*s+1)))
      (⟨[],false,List.replicate (aDoubleUnary t s) true ++
        (false :: List.replicate 6 true),5⟩ : Cfg) := by
  have hfirst : run (firstTime (3*t) (3*s+1))
      (input (3*t) (3*s+1)) = postZ (3*t) (3*s+1) := by
    simpa only [firstTime,input,postZ,List.append_nil,List.cons_append] using
      (BB6.Agent36EZeroZTwo.full_E_zero_pairs_all (3*t) (3*s+1) [])
  rw [run_add,hfirst]
  exact a_follow_plus_one t s

/-- Another universal E-q0 exceptional-terminal family closes to unary. -/
theorem a_two_return_plus_two (t s : Nat) :
    ObsEq (run (firstTime (3*t) (3*s+2)+aExtraTime t s)
      (input (3*t) (3*s+2)))
      (⟨[],false,List.replicate (aExtraUnary t s) true,5⟩ : Cfg) := by
  have hfirst : run (firstTime (3*t) (3*s+2))
      (input (3*t) (3*s+2)) = postZ (3*t) (3*s+2) := by
    simpa only [firstTime,input,postZ,List.append_nil,List.cons_append] using
      (BB6.Agent36EZeroZTwo.full_E_zero_pairs_all (3*t) (3*s+2) [])
  rw [run_add,hfirst]
  exact a_follow_plus_two t s

#print axioms a_two_return_plus_one
#print axioms a_two_return_plus_two
#print axioms a_follow_plus_one
#print axioms a_follow_plus_two

#print axioms a_follow_multiple_three
#print axioms a_two_return_multiple_three
end BB6.Agent36EZeroZTwoA
