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

private theorem output_input (t p : Nat) :
    BB6.Agent32EAll.output (3*t+2) (3*p+2) [] =
      init (List.replicate (3*(K t)+1) true ++
        false :: (CryptidA.wordCode (words p) ++ (false :: ys))) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(K t)+1) := by dsimp [K]; omega
  have hr : List.replicate (8*(3*t+2)+5) true =
      true::true::List.replicate (3*(K t)+1) true := by
    rw [hn]
    calc
      _ = List.replicate 2 true ++ List.replicate (3*(K t)+1) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [BB6.Agent32EAll.output, List.append_nil]
  rw [hr]
  have hq : 2*(3*p+2)+2 = 6*(p+1) := by omega
  rw [hq,←word_shape p]
  simp [init,ys,List.append_assoc]

private theorem output_target (t p : Nat) :
    (⟨[],false,
      List.replicate (2*(4*(K t)+3+CryptidA.wordInc (words p))+5) true ++ ys, 5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨64*t+65+16*(p+1),0,0⟩ := by
  have hi : CryptidA.wordInc (words p) = 8*(p+1) := word_inc p
  have hn : (2*(4*(K t)+3+8*(p+1))+5)+6=64*t+65+16*(p+1) := by dsimp [K]; omega
  have hrep : List.replicate (2*(4*(K t)+3+CryptidA.wordInc (words p))+5) true ++ ys =
      List.replicate (64*t+65+16*(p+1)) true := by
    rw [hi]
    simp only [ys,List.replicate_append_replicate]
    congr 1
  have hfront : List.replicate (64*t+65+16*(p+1)) true =
      true :: true :: List.replicate (64*t+63+16*(p+1)) true := by
    calc
      _ = List.replicate (2+(64*t+63+16*(p+1))) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+63+16*(p+1)) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  simp only [DRegularSource.sourceSection,init,oppairs,List.replicate_zero,
    List.nil_append,List.append_nil,
    show (64*t+65+16*(p+1))-2=64*t+63+16*(p+1) by omega]
  rw [hrep,hfront]

theorem rejoin (t p : Nat) :
    run (aCost t p) (BB6.Agent32EAll.output (3*t+2) (3*p+2) []) =
      DRegularSource.sourceSection ⟨64*t+65+16*(p+1),0,0⟩ := by
  rw [output_input]
  exact Eq.trans (BB6.Agent35.full_A_code (K t) (words p) ys) (output_target t p)

theorem e_input (t p : Nat) :
    DRegularSource.sourceSection ⟨9*t+10,3*(p+1),1⟩ =
      init (List.replicate (3*(3*t+2)+2) true ++
        false :: (pairs (3*p+2) ++ [true,true])) := by
  have hn : (9*t+10)-2=3*(3*t+2)+2 := by omega
  have hp : 3*(p+1)=(3*p+2)+1 := by omega
  simp only [DRegularSource.sourceSection,init,hn,hp,List.replicate_one]
  rw [List.append_assoc,BB6.Agent25BGeneral.oppairs_last]

/-- Every k≡2 (mod3) E-exception with q divisible by 3 has an exact
    two-return original-source reentry into the pure unary regular language. -/
theorem exceptional_EA_general (t p : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) (3*p+2) + aCost t p)
        (DRegularSource.sourceSection ⟨9*t+10,3*(p+1),1⟩))
      (DRegularSource.sourceSection ⟨64*t+65+16*(p+1),0,0⟩) := by
  have hi : ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) (3*p+2))
        (DRegularSource.sourceSection ⟨9*t+10,3*(p+1),1⟩))
      (BB6.Agent32EAll.output (3*t+2) (3*p+2) []) := by
    rw [e_input]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) (3*p+2)
  have hA := source_congr (aCost t p) hi
  rw [rejoin] at hA
  simpa only [run_add] using hA

#print axioms exceptional_EA_general
end BB6.Agent25AGeneral
