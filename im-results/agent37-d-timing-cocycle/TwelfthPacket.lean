import Lean.Elab.Tactic.Omega
import ExceptionalBGeneral
import A110111CodeFirst
import EAllDouble
import BoundaryPadding

set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent37TwelfthPacket

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private def words : List Bool := List.replicate 4 true
private def tail3 : List Bool := List.replicate 3 true

def sourceStart (t : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨9*t+10,7,1⟩

def sourceEnd (t : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨64*t+91,3,2⟩

def eCost (t : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t+2) 6

def aCost (t : Nat) : Nat :=
  let K := 8*t+6
  let m := 4*K+3+CryptidA.wordInc words
  (12*K*K+41*K+32)+
    (CryptidA.wordCost (4*K+3) words+(2*m+24))

def totalTime (t : Nat) := eCost t+aCost t

private theorem e_start_shape (t : Nat) :
    sourceStart t =
      init (List.replicate (3*(3*t+2)+2) true ++
        false :: (pairs 6 ++ [true,true])) := by
  have hn : 9*t+10-2=3*(3*t+2)+2 := by omega
  have hp : (7:Nat) = 6+1 := by omega
  simp only [sourceStart, DRegularSource.sourceSection, hn, hp,
    List.replicate_one]
  rw [List.append_assoc,BB6.Agent25BGeneral.oppairs_last]

private theorem word_shape :
    CryptidA.wordCode words = List.replicate 12 true := by decide

private theorem word_inc :
    CryptidA.wordInc words = 16 := by decide

private theorem e_mid_shape (t : Nat) :
    BB6.Agent32EAll.output (3*t+2) 6 [] =
      init (List.replicate (3*(8*t+6)+1) true ++
        false :: (CryptidA.wordCode words ++
          BB6.CryptidA110111CodeFirst.packet tail3)) := by
  have hn : 8*(3*t+2)+5 = 3*(8*t+6)+3 := by omega
  have hr : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    rw [hn,show 3*(8*t+6)+3=2+(3*(8*t+6)+1) by omega]
    rw [← List.replicate_append_replicate]
    rfl
  simp only [BB6.Agent32EAll.output,List.append_nil]
  rw [hr]
  simp [init, word_shape, tail3,
    BB6.CryptidA110111CodeFirst.packet, List.append_assoc]

private theorem a_end_shape (t : Nat) :
    (⟨[],false,
      List.replicate (2*(4*(8*t+6)+3+CryptidA.wordInc words)+5) true ++
        BB6.CryptidA110111CodeFirst.tail tail3,5⟩ : Cfg) =
      sourceEnd t := by
  have hn : 2*(4*(8*t+6)+3+16)+5=64*t+91 := by omega
  have hr : List.replicate (64*t+91) true =
      true :: true :: List.replicate (64*t+89) true := by
    rw [show 64*t+91=2+(64*t+89) by omega,
      ←List.replicate_append_replicate]
    rfl
  have htail : BB6.CryptidA110111CodeFirst.tail tail3 =
      oppairs 3 ++ List.replicate 2 true := by decide
  simp only [sourceEnd, DRegularSource.sourceSection,
    show 64*t+91-2=64*t+89 by omega,word_inc, hn]
  rw [htail,hr]
  simp [init,List.append_assoc]

/-- Original six-state, all-natural, two exact return endpoints for the
    k=3t+2, q=7 exceptional E branch. The second A terminal is 110111,
    following four 111 tokens and a physically implicit blank ending. -/
theorem two_returns (t : Nat) :
    ObsEq (run (totalTime t) (sourceStart t)) (sourceEnd t) := by
  have hE : ObsEq
      (run (eCost t) (sourceStart t))
      (BB6.Agent32EAll.output (3*t+2) 6 []) := by
    rw [e_start_shape]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) 6
  have hA : run (aCost t)
      (BB6.Agent32EAll.output (3*t+2) 6 []) = sourceEnd t := by
    rw [e_mid_shape]
    simpa only [aCost, a_end_shape] using
      (BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return
        (8*t+6) words tail3).1
  simpa only [totalTime] using
    (source_chain (eCost t) (aCost t)
      (sourceStart t)
      (BB6.Agent32EAll.output (3*t+2) 6 [])
      (sourceEnd t) hE (by rw [hA]; exact cfgEq_refl _))

#print axioms two_returns
end BB6.Agent37TwelfthPacket
