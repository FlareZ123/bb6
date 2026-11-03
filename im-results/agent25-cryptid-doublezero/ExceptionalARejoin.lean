import Lean.Elab.Tactic.Omega
import ExceptionalBRejoin
import ABridgeCode

set_option maxHeartbeats 5000000
namespace BB6.Agent25ARejoin
open CryptidBoundary

def K (t : Nat) : Nat := 8*t+6
def w4 : List Bool := [true,true,true,true]
def ys : List Bool := List.replicate 6 true
def aCost (t : Nat) : Nat :=
  (12*(K t)*(K t)+41*(K t)+32) +
    (CryptidA.wordCost (4*(K t)+3) w4 +
      (2*(4*(K t)+3+CryptidA.wordInc w4)+6))

private theorem code_four :
    CryptidA.wordCode w4 = List.replicate 12 true := by decide
private theorem increment_four : CryptidA.wordInc w4 = 16 := by decide

private theorem source_input (t : Nat) :
    BB6.Agent32EAll.output (3*t+2) 5 [] =
      init (List.replicate (3*(K t)+1) true ++
        false :: (CryptidA.wordCode w4 ++ (false :: ys))) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(K t)+1) := by dsimp [K]; omega
  have hr : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(K t)+1) true := by
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(K t)+1) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [BB6.Agent32EAll.output, List.append_nil]
  rw [hr]
  simp [init, code_four, ys, List.append_assoc]

private theorem source_output (t : Nat) :
    (⟨[],false,
      List.replicate (2*(4*(K t)+3+CryptidA.wordInc w4)+5) true ++ ys, 5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨64*t+97,0,0⟩ := by
  have hw : CryptidA.wordInc w4 = 16 := increment_four
  have hn : (2*(4*(K t)+3+16)+5)+6=64*t+97 := by dsimp [K]; omega
  have hrep : List.replicate (2*(4*(K t)+3+CryptidA.wordInc w4)+5) true ++ ys =
      List.replicate (64*t+97) true := by
    rw [hw]
    simp only [ys,List.replicate_append_replicate]
    congr 1
  have hfront : List.replicate (64*t+97) true =
      true :: true :: List.replicate (64*t+95) true := by
    calc
      _ = List.replicate (2+(64*t+95)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+95) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [DRegularSource.sourceSection, init, oppairs,
    List.replicate_zero, List.nil_append, List.append_nil,
    show 64*t+97-2=64*t+95 by omega]
  rw [hrep,hfront]

/-- The second E-exception, k=3t+2 and q=6, returns to pure unary.
    Both exact raw source transitions are uniform in t. -/
theorem exceptional_A_rejoins_unary (t : Nat) :
    run (aCost t) (BB6.Agent32EAll.output (3*t+2) 5 []) =
      DRegularSource.sourceSection ⟨64*t+97,0,0⟩ := by
  rw [source_input]
  simpa only [aCost,K,w4,ys] using
    (Eq.trans (BB6.Agent35.full_A_code (K t) w4 ys) (source_output t))

/-- Original-source physical rejoin of the k≡2 (mod3) E exception into
    the regular pure-unary language, with implicit infinite blank zeros. -/
theorem exceptional_EA_two_source (t : Nat) :
    BB6.BoundaryPadding.ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) 5 + aCost t)
        (DRegularSource.sourceSection ⟨9*t+10,6,1⟩))
      (DRegularSource.sourceSection ⟨64*t+97,0,0⟩) := by
  have hin : DRegularSource.sourceSection ⟨9*t+10,6,1⟩ =
      init (List.replicate (3*(3*t+2)+2) true ++
        (false :: (pairs 5 ++ [true,true]))) := by
    have hn : (9*t+10)-2=3*(3*t+2)+2 := by omega
    simp [DRegularSource.sourceSection,hn,oppairs,pairs,List.append_assoc]
  have hE : BB6.BoundaryPadding.ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) 5)
        (DRegularSource.sourceSection ⟨9*t+10,6,1⟩))
      (BB6.Agent32EAll.output (3*t+2) 5 []) := by
    rw [hin]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) 5
  have hA := BB6.BoundaryPadding.source_congr (aCost t) hE
  rw [exceptional_A_rejoins_unary] at hA
  simpa only [run_add] using hA

#print axioms exceptional_A_rejoins_unary
#print axioms exceptional_EA_two_source
end BB6.Agent25ARejoin
