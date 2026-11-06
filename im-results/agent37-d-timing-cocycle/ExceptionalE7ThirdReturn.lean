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

private def suffix2 (r : Nat) : List Bool :=
  List.replicate (6*r-1) true ++ (false :: List.replicate 6 true)

private def codeWords (r : Nat) : List Bool :=
  [false,false] ++ List.replicate (2*r-1) true

private def suffix3 : List Bool := List.replicate 3 true

def sourceStart (u r : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨27*u+7,3*r+1,1⟩

def sourceEnd (u r : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨8*(64*u+10)+16*r+7,3,2⟩

def eTime (u r : Nat) : Nat :=
  BB6.Agent32EAll.duration (9*u+1) (3*r)

def middleTime (u : Nat) : Nat :=
  12*(24*u+3)*(24*u+3)+49*(24*u+3)+58

def aTime (u r : Nat) : Nat :=
  (12*(64*u+10)*(64*u+10)+41*(64*u+10)+32) +
    (CryptidA.wordCost (4*(64*u+10)+3) (codeWords r) +
      (2*((4*(64*u+10)+3)+CryptidA.wordInc (codeWords r))+24))

def totalTime (u r : Nat) : Nat :=
  eTime u r + (middleTime u + aTime u r)

private theorem e_start_shape (u r : Nat) :
    sourceStart u r =
      init (List.replicate (3*(9*u+1)+2) true ++
        false :: (pairs (3*r) ++ [true,true])) := by
  have hn : 27*u+7-2=3*(9*u+1)+2 := by omega
  simp only [sourceStart,DRegularSource.sourceSection,init,hn,
    List.replicate_one]
  rw [List.append_assoc,BB6.Agent25BGeneral.oppairs_last]

private theorem first_mid_shape (u r : Nat) (hr : 1 ≤ r) :
    BB6.Agent32EAll.output (9*u+1) (3*r) [] =
      init (List.replicate (3*(24*u+3)+2) true ++
        false :: ([true,true,true] ++ suffix2 r)) := by
  have hn : 8*(9*u+1)+5=3*(24*u+3)+4 := by omega
  have hrp : 2*(3*r)+2=3+(6*r-1) := by omega
  have hrep : List.replicate (8*(9*u+1)+5) true =
      true::true::List.replicate (3*(24*u+3)+2) true := by
    rw [hn,show 3*(24*u+3)+4=2+(3*(24*u+3)+2) by omega]
    rw [←List.replicate_append_replicate]
    rfl
  have hp : List.replicate (2*(3*r)+2) true =
      [true,true,true] ++ List.replicate (6*r-1) true := by
    rw [hrp,←List.replicate_append_replicate]
    rfl
  simp only [BB6.Agent32EAll.output,List.append_nil]
  rw [hrep,hp]
  simp [init,suffix2,List.append_assoc]

private def secondOutput (u r : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*(24*u+3)+9) true ++
    (CryptidBoundary.packetThree ++ suffix2 r),5⟩

private theorem second_return (u r : Nat) (hr : 1 ≤ r) :
    run (middleTime u) (BB6.Agent32EAll.output (9*u+1) (3*r) []) =
      secondOutput u r := by
  rw [first_mid_shape u r hr]
  exact CryptidBoundary.full_E_three (24*u+3) (suffix2 r)

private theorem second_a_shape (u r : Nat) (hr : 1 ≤ r) :
    secondOutput u r =
      init (List.replicate (3*(64*u+10)+1) true ++
        false :: (CryptidA.wordCode (codeWords r) ++
          CryptidA110111CodeFirst.packet suffix3)) := by
  have hn : 8*(24*u+3)+9=3*(64*u+10)+3 := by omega
  have hw : CryptidA.wordCode (codeWords r) =
      [true,false,true,false] ++ List.replicate (6*r-3) true := by
    simp [codeWords,CryptidA.wordCode,List.replicate_append_replicate]
  rw [hn,hw]
  simp [secondOutput,init,CryptidBoundary.packetThree,suffix2,suffix3,
    codeWords,CryptidA110111CodeFirst.packet,List.append_assoc]

private theorem a_end_shape (u r : Nat) (hr : 1 ≤ r) :
    (⟨[],false,
      List.replicate
        (2*(4*(64*u+10)+3+CryptidA.wordInc (codeWords r))+5) true ++
        CryptidA110111CodeFirst.tail suffix3,5⟩ : Cfg) =
      sourceEnd u r := by
  have hi : CryptidA.wordInc (codeWords r) = 8*r-2 := by
    simp [codeWords,CryptidA.wordInc]
    omega
  have ht :
      CryptidA110111CodeFirst.tail suffix3 =
        BB6.Agent25BGeneral.oppairs 3 ++ [true,true] := by decide
  have hrep :
      List.replicate
        (2*(4*(64*u+10)+3+CryptidA.wordInc (codeWords r))+5) true ++
          CryptidA110111CodeFirst.tail suffix3 =
      List.replicate (8*(64*u+10)+16*r+7) true ++
          (BB6.Agent25BGeneral.oppairs 3 ++ [true,true]) := by
    rw [hi,ht]
    congr 1
    omega
  have hfront :
      List.replicate (8*(64*u+10)+16*r+7) true =
        true::true::List.replicate (8*(64*u+10)+16*r+5) true := by
    rw [show 8*(64*u+10)+16*r+7 =
      2+(8*(64*u+10)+16*r+5) by omega,
      ←List.replicate_append_replicate]
    rfl
  simp only [sourceEnd,DRegularSource.sourceSection,init,oppairs,
    List.replicate_one,
    show (8*(64*u+10)+16*r+7)-2=8*(64*u+10)+16*r+5 by omega]
  rw [hrep,hfront]

private theorem third_return (u r : Nat) (hr : 1 ≤ r) :
    run (aTime u r) (secondOutput u r) = sourceEnd u r := by
  rw [second_a_shape u r hr]
  simpa only [aTime,sourceEnd,a_end_shape u r hr] using
    (BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return
      (64*u+10) (codeWords r) suffix3)

private theorem first_return (u r : Nat) :
    BB6.BoundaryPadding.ObsEq
      (run (eTime u r) (sourceStart u r))
      (BB6.Agent32EAll.output (9*u+1) (3*r) []) := by
  rw [e_start_shape]
  exact BB6.Agent32EAll.all_e_double_implicit_blank (9*u+1) (3*r)

 /-- The k≡1 (mod 3), q=3r+1 synthetic E exception has three exact
    original-source returns when t is divisible by 3. The third A-coded
    return rejoins the DRegular language at L(a,3,2). -/
theorem exceptional_EEA_rejoin (u r : Nat) (hr : 1 ≤ r) :
    BB6.BoundaryPadding.ObsEq
      (run (totalTime u r) (sourceStart u r))
      (sourceEnd u r) := by
  have h1 := first_return u r
  have h2 : BB6.BoundaryPadding.ObsEq
      (run (middleTime u) (BB6.Agent32EAll.output (9*u+1) (3*r) []))
      (secondOutput u r) := by
    rw [second_return u r hr]
    exact cfgEq_refl _
  have h3 : BB6.BoundaryPadding.ObsEq
      (run (aTime u r) (secondOutput u r)) (sourceEnd u r) := by
    rw [third_return u r hr]
    exact cfgEq_refl _
  have h23 := source_chain (middleTime u) (aTime u r)
    (BB6.Agent32EAll.output (9*u+1) (3*r) []) (secondOutput u r)
    (sourceEnd u r) h2 h3
  exact source_chain (eTime u r) (middleTime u+aTime u r)
    (sourceStart u r) (BB6.Agent32EAll.output (9*u+1) (3*r) [])
    (sourceEnd u r) h1 h23

#print axioms exceptional_EEA_rejoin

end BB6.Agent2E7ThirdReturn
