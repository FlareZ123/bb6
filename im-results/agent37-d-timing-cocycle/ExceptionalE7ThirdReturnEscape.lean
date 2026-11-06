import Lean.Elab.Tactic.Omega
import BlankThirteenthRejoin
import EAllDouble
import CryptidThree
import CryptidTriplePairs
import DObsSourceCandidate

set_option maxHeartbeats 100000000
set_option maxRecDepth 16384

namespace BB6.Agent2E7ThirdReturnEscape

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private def suffix2 (q : Nat) : List Bool :=
  List.replicate (2*q-3) true ++ (false :: List.replicate 6 true)

private def suffix3 (q : Nat) : List Bool :=
  List.replicate (2*q-6) true ++ (false :: List.replicate 6 true)

def sourceStart (u q : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨27*u+16,q,1⟩

def sourceEnd (u q : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*(64*u+31)+9) true ++
    (CryptidBoundary.oppairs 4 ++ (false :: suffix3 q)),5⟩

def eTime (u q : Nat) : Nat :=
  BB6.Agent32EAll.duration (9*u+4) (q-1)

def middleTime (u : Nat) : Nat :=
  12*(24*u+11)*(24*u+11)+49*(24*u+11)+58

def thirdTime (u : Nat) : Nat :=
  12*(64*u+31)*(64*u+31)+49*(64*u+31)+70

def totalTime (u q : Nat) : Nat :=
  eTime u q + (middleTime u + thirdTime u)

private theorem e_start_shape (u q : Nat) (hq : 3 ≤ q) :
    sourceStart u q =
      init (List.replicate (3*(9*u+4)+2) true ++
        false :: (pairs (q-1) ++ [true,true])) := by
  have hn : 27*u+16-2=3*(9*u+4)+2 := by omega
  have ho : CryptidBoundary.oppairs q =
      CryptidBoundary.oppairs (q-1+1) := by
    congr 1
    omega
  simp only [sourceStart,DRegularSource.sourceSection,init,hn,
    List.replicate_one]
  rw [List.append_assoc,ho,BB6.Agent25BGeneral.oppairs_last]

private theorem first_mid_shape (u q : Nat) (hq : 3 ≤ q) :
    BB6.Agent32EAll.output (9*u+4) (q-1) [] =
      init (List.replicate (3*(24*u+11)+2) true ++
        false :: ([true,true,true] ++ suffix2 q)) := by
  have hn : 8*(9*u+4)+5=3*(24*u+11)+4 := by omega
  have hqrep : 2*(q-1)+2=3+(2*q-3) := by omega
  have hrep : List.replicate (8*(9*u+4)+5) true =
      true::true::List.replicate (3*(24*u+11)+2) true := by
    rw [hn,show 3*(24*u+11)+4=2+(3*(24*u+11)+2) by omega]
    rw [←List.replicate_append_replicate]
    rfl
  have hp : List.replicate (2*(q-1)+2) true =
      [true,true,true] ++ List.replicate (2*q-3) true := by
    rw [hqrep,←List.replicate_append_replicate]
    rfl
  simp only [BB6.Agent32EAll.output,List.append_nil]
  rw [hrep,hp]
  simp [init,suffix2,List.append_assoc]

private def secondOutput (u q : Nat) : Cfg :=
  ⟨[],false,List.replicate (8*(24*u+11)+9) true ++
    (CryptidBoundary.packetThree ++ suffix2 q),5⟩

private theorem second_return (u q : Nat) (hq : 3 ≤ q) :
    run (middleTime u) (BB6.Agent32EAll.output (9*u+4) (q-1) []) =
      secondOutput u q := by
  rw [first_mid_shape u q hq]
  exact CryptidBoundary.full_E_three (24*u+11) (suffix2 q)

private theorem second_a_shape (u q : Nat) (hq : 3 ≤ q) :
    secondOutput u q =
      init (List.replicate (3*(64*u+31)+2) true ++
        false :: (pairs 2 ++ [true,true,true] ++ suffix3 q)) := by
  have hn : 8*(24*u+11)+9=3*(64*u+31)+4 := by omega
  have hrep : List.replicate (2*q-3) true =
      [true,true,true] ++ List.replicate (2*q-6) true := by
    rw [show 2*q-3=3+(2*q-6) by omega,
      ←List.replicate_append_replicate]
    simp [List.replicate]
  simp only [secondOutput,CryptidBoundary.packetThree,suffix2,suffix3]
  rw [hn,hrep]
  have hfront : List.replicate (3*(64*u+31)+4) true =
      true::true::List.replicate (3*(64*u+31)+2) true := by
    rw [show 3*(64*u+31)+4 =
      2+(3*(64*u+31)+2) by omega,
      ←List.replicate_append_replicate]
    simp [List.replicate]
  rw [hfront]
  simp [init,pairs]

private theorem third_return (u q : Nat) (hq : 3 ≤ q) :
    run (thirdTime u) (secondOutput u q) = sourceEnd u q := by
  rw [second_a_shape u q hq]
  exact BB6.CryptidTriplePairs.full_E_triple_pairs
    (64*u+31) 2 (suffix3 q)

private theorem first_return (u q : Nat) (hq : 3 ≤ q) :
    BB6.BoundaryPadding.ObsEq
      (run (eTime u q) (sourceStart u q))
      (BB6.Agent32EAll.output (9*u+4) (q-1) []) := by
  rw [e_start_shape u q hq]
  exact BB6.Agent32EAll.all_e_double_implicit_blank (9*u+4) (q-1)

/-- For k=3t+1 with t=3u+1 and q≥3, three exact original-source
    E returns reach the off-L packet P₄ 0 1^(2q-6) 0 1⁶. -/
theorem exceptional_EEE_escape (u q : Nat) (hq : 3 ≤ q) :
    BB6.BoundaryPadding.ObsEq
      (run (totalTime u q) (sourceStart u q))
      (sourceEnd u q) := by
  have h1 := first_return u q hq
  have h2 : BB6.BoundaryPadding.ObsEq
      (run (middleTime u) (BB6.Agent32EAll.output (9*u+4) (q-1) []))
      (secondOutput u q) := by
    rw [second_return u q hq]
    exact cfgEq_refl _
  have h3 : BB6.BoundaryPadding.ObsEq
      (run (thirdTime u) (secondOutput u q)) (sourceEnd u q) := by
    rw [third_return u q hq]
    exact cfgEq_refl _
  have h23 := source_chain (middleTime u) (thirdTime u)
    (BB6.Agent32EAll.output (9*u+4) (q-1) []) (secondOutput u q)
    (sourceEnd u q) h2 h3
  exact source_chain (eTime u q) (middleTime u+thirdTime u)
    (sourceStart u q) (BB6.Agent32EAll.output (9*u+4) (q-1) [])
    (sourceEnd u q) h1 h23

#print axioms exceptional_EEE_escape

end BB6.Agent2E7ThirdReturnEscape
