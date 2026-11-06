import Lean.Elab.Tactic.Omega
import BlankThirteenthRejoin
import EAllDouble
import CryptidThree
import ABridgeCode
import A110111CodeFirst
import DObsSourceCandidate

set_option maxHeartbeats 100000000
set_option maxRecDepth 16384

namespace BB6.Agent2E7ThirdReturn

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private def suffix2 : List Bool :=
  List.replicate 11 true ++ (false :: List.replicate 6 true)

private def codeWords : List Bool := [false,false,true,true,true]
private def suffix3 : List Bool := List.replicate 3 true

def sourceStart (u : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨27*u+7,7,1⟩

def sourceEnd (u : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨8*(64*u+10)+39,3,2⟩

def eTime (u : Nat) : Nat :=
  BB6.Agent32EAll.duration (9*u+1) 6

def middleTime (u : Nat) : Nat :=
  12*(24*u+3)*(24*u+3)+49*(24*u+3)+58

def aTime (u : Nat) : Nat :=
  (12*(64*u+10)*(64*u+10)+41*(64*u+10)+32) +
    (CryptidA.wordCost (4*(64*u+10)+3) codeWords +
      (2*((4*(64*u+10)+3)+CryptidA.wordInc codeWords)+24))

def totalTime (u : Nat) : Nat :=
  eTime u + (middleTime u + aTime u)

private theorem e_start_shape (u : Nat) :
    sourceStart u =
      init (List.replicate (3*(9*u+1)+2) true ++
        false :: (pairs 6 ++ [true,true])) := by
  have hn : 27*u+7-2=3*(9*u+1)+2 := by omega
  simp only [sourceStart,DRegularSource.sourceSection,init,hn,
    List.replicate_one]
  rw [List.append_assoc,BB6.Agent25BGeneral.oppairs_last]

private theorem first_mid_shape (u : Nat) :
    BB6.Agent32EAll.output (9*u+1) 6 [] =
      init (List.replicate (3*(24*u+3)+2) true ++
        false :: ([true,true,true] ++ suffix2)) := by
  have hn : 8*(9*u+1)+5=3*(24*u+3)+4 := by omega
  have hr : List.replicate (8*(9*u+1)+5) true =
      true::true::List.replicate (3*(24*u+3)+2) true := by
    rw [hn,show 3*(24*u+3)+4=2+(3*(24*u+3)+2) by omega]
    rw [←List.replicate_append_replicate]
    rfl
  have hp : List.replicate 14 true =
      [true,true,true] ++ List.replicate 11 true := by
    rw [show 14=3+11 by omega,←List.replicate_append_replicate]
    rfl
  simp only [BB6.Agent32EAll.output,List.append_nil]
  rw [hr,hp]
  simp [init,suffix2,List.append_assoc]

private def secondOutput (u : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*(24*u+3)+9) true ++
    (CryptidBoundary.packetThree ++ suffix2),5⟩

private theorem second_return (u : Nat) :
    run (middleTime u) (BB6.Agent32EAll.output (9*u+1) 6 []) =
      secondOutput u := by
  rw [first_mid_shape]
  exact CryptidBoundary.full_E_three (24*u+3) suffix2

private theorem second_a_shape (u : Nat) :
    secondOutput u =
      init (List.replicate (3*(64*u+10)+1) true ++
        false :: (CryptidA.wordCode codeWords ++
          CryptidA110111CodeFirst.packet suffix3)) := by
  have hn : 8*(24*u+3)+9=3*(64*u+10)+3 := by omega
  have hw : CryptidA.wordCode codeWords =
      [true,false,true,false] ++ List.replicate 9 true := by decide
  rw [hn,hw]
  simp [secondOutput,init,CryptidBoundary.packetThree,suffix2,suffix3,
    CryptidA110111CodeFirst.packet,List.append_assoc]

private theorem a_end_shape (u : Nat) :
    (⟨[],false,
      List.replicate
        (2*(4*(64*u+10)+3+CryptidA.wordInc codeWords)+5) true ++
        CryptidA110111CodeFirst.tail suffix3,5⟩ : Cfg) =
      sourceEnd u := by
  have hi : CryptidA.wordInc codeWords = 14 := by decide
  have ht :
      CryptidA110111CodeFirst.tail suffix3 =
        BB6.Agent25BGeneral.oppairs 3 ++ [true,true] := by decide
  have hrep :
      List.replicate
        (2*(4*(64*u+10)+3+CryptidA.wordInc codeWords)+5) true ++
          CryptidA110111CodeFirst.tail suffix3 =
      List.replicate (8*(64*u+10)+39) true ++
          (BB6.Agent25BGeneral.oppairs 3 ++ [true,true]) := by
    rw [hi,ht]
    congr 1
    omega
  have hfront : List.replicate (8*(64*u+10)+39) true =
      true::true::List.replicate (8*(64*u+10)+37) true := by
    rw [show 8*(64*u+10)+39 =
      2+(8*(64*u+10)+37) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp only [sourceEnd,DRegularSource.sourceSection,init,oppairs,
    List.replicate_one,
    show (8*(64*u+10)+39)-2=8*(64*u+10)+37 by omega]
  rw [hrep,hfront]

private theorem third_return (u : Nat) :
    run (aTime u) (secondOutput u) = sourceEnd u := by
  rw [second_a_shape]
  simpa only [aTime,sourceEnd,a_end_shape] using
    (BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return
      (64*u+10) codeWords suffix3)

private theorem first_return (u : Nat) :
    BB6.BoundaryPadding.ObsEq
      (run (eTime u) (sourceStart u))
      (BB6.Agent32EAll.output (9*u+1) 6 []) := by
  rw [e_start_shape]
  exact BB6.Agent32EAll.all_e_double_implicit_blank (9*u+1) 6

/-- The k≡1 (mod 3), q=7 synthetic E exception has three exact
    original-source returns when t is divisible by 3. The third A-coded
    return rejoins the DRegular language at L(a,3,2). -/
theorem exceptional_EEA_rejoin (u : Nat) :
    BB6.BoundaryPadding.ObsEq
      (run (totalTime u) (sourceStart u))
      (sourceEnd u) := by
  have h1 := first_return u
  have h2 : BB6.BoundaryPadding.ObsEq
      (run (middleTime u) (BB6.Agent32EAll.output (9*u+1) 6 []))
      (secondOutput u) := by
    rw [second_return]
    exact cfgEq_refl _
  have h3 : BB6.BoundaryPadding.ObsEq
      (run (aTime u) (secondOutput u)) (sourceEnd u) := by
    rw [third_return]
    exact cfgEq_refl _
  have h23 := source_chain (middleTime u) (aTime u)
    (BB6.Agent32EAll.output (9*u+1) 6 []) (secondOutput u)
    (sourceEnd u) h2 h3
  exact source_chain (eTime u) (middleTime u+aTime u)
    (sourceStart u) (BB6.Agent32EAll.output (9*u+1) 6 [])
    (sourceEnd u) h1 h23

#print axioms exceptional_EEA_rejoin

end BB6.Agent2E7ThirdReturn
