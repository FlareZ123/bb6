import Lean.Elab.Tactic.Omega
import EAMultiplesSource
import CodeImplicitNil

set_option maxHeartbeats 35000000
set_option maxRecDepth 8192

namespace BB6.EAResidueTwoSource
open CryptidBoundary BB6.BoundaryPadding

private def code (v : Nat) : List Bool :=
  List.replicate (2*v+1) true ++ [false,true,true]
private def kA (t : Nat) := 8*t+6
private def costA (t v : Nat) :=
  (12*(kA t)*(kA t)+41*(kA t)+32) +
    (CryptidA.wordCost (4*(kA t)+3) (code v) +
      (2*((4*(kA t)+3)+CryptidA.wordInc (code v))+6))

private theorem code_append (xs ys : List Bool) :
    CryptidA.wordCode (xs ++ ys) =
      CryptidA.wordCode xs ++ CryptidA.wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [CryptidA.wordCode,ih,List.append_assoc]

private theorem inc_append (xs ys : List Bool) :
    CryptidA.wordInc (xs ++ ys) =
      CryptidA.wordInc xs + CryptidA.wordInc ys := by
  induction xs with
  | nil => simp [CryptidA.wordInc]
  | cons b xs ih =>
    cases b <;> simp [CryptidA.wordInc,ih, Nat.add_assoc]

private theorem code_ones (n : Nat) :
    CryptidA.wordCode (List.replicate n true) =
      List.replicate (3*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true,true] ++
      CryptidA.wordCode (List.replicate n true) =
      List.replicate (3*(n+1)) true
    rw [ih,show 3*(n+1)=3+3*n by omega,
      ← List.replicate_append_replicate]
    rfl

private theorem inc_ones (n : Nat) :
    CryptidA.wordInc (List.replicate n true) = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 4 + CryptidA.wordInc (List.replicate n true) = 4*(n+1)
    rw [ih]
    omega

private theorem code_word (v : Nat) :
    CryptidA.wordCode (code v) =
      List.replicate (6*v+4) true ++
        (false :: List.replicate 6 true) := by
  rw [code,code_append,code_ones]
  change List.replicate (3*(2*v+1)) true ++
      ([true,false] ++ [true,true,true] ++ [true,true,true]) =
    List.replicate (6*v+4) true ++ (false::List.replicate 6 true)
  have hr : List.replicate (3*(2*v+1)) true ++ [true] =
      List.replicate (6*v+4) true := by
    calc
      _ = List.replicate (3*(2*v+1)) true ++
          List.replicate 1 true := rfl
      _ = List.replicate (3*(2*v+1)+1) true :=
        List.replicate_append_replicate
      _ = _ := by congr 1; omega
  calc
    _ = (List.replicate (3*(2*v+1)) true ++ [true]) ++
          (false::List.replicate 6 true) := by simp [List.append_assoc]
    _ = _ := by rw [hr]

private theorem inc_word (v : Nat) :
    CryptidA.wordInc (code v) = 8*v+13 := by
  rw [code,inc_append,inc_ones]
  change 4*(2*v+1) + (1+4+4) = 8*v+13
  omega

private theorem oppairs_to_pairs (q : Nat) :
    oppairs (q+1) ++ [true] =
      false :: (pairs q ++ [true,true]) := by
  calc
    oppairs (q+1) ++ [true] =
        false :: ((true :: oppairs q) ++ [true]) := rfl
    _ = false :: ((pairs q ++ [true]) ++ [true]) := by
      rw [BB6.AOneSource.one_oppairs q]
    _ = false :: (pairs q ++ [true,true]) := by simp [List.append_assoc]

private theorem start_E (t v : Nat) :
    DRegularSource.sourceSection ⟨9*t+10,3*v+2,1⟩ =
      init (List.replicate (3*(3*t+2)+2) true ++
        (false :: (pairs (3*v+1) ++ [true,true]))) := by
  have hn : (9*t+10)-2=3*(3*t+2)+2 := by omega
  have hword : oppairs (3*v+2) ++ List.replicate 1 true =
      false :: (pairs (3*v+1) ++ [true,true]) := by
    simpa only [List.replicate_one,
      show (3*v+1)+1=3*v+2 by omega] using
      (oppairs_to_pairs (3*v+1))
  simp only [DRegularSource.sourceSection, hn, List.replicate_one]
  rw [List.append_assoc, hword]

private theorem after_E (t v : Nat) :
    BB6.Agent32EAll.output (3*t+2) (3*v+1) [] =
      init (List.replicate (3*(kA t)+1) true ++
        (false :: CryptidA.wordCode (code v))) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(kA t)+1) := by
    dsimp [kA]
    omega
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true::true::List.replicate (3*(kA t)+1) true := by
    calc
      _ = List.replicate (2+(3*(kA t)+1)) true := by rw [hn]
      _ = List.replicate 2 true ++
          List.replicate (3*(kA t)+1) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  have hc : CryptidA.wordCode (code v) =
      List.replicate (2*(3*v+1)+2) true ++
        (false :: List.replicate 6 true) := by
    rw [code_word]
    congr 1
    omega
  change (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
    (false :: List.replicate (2*(3*v+1)+2) true ++
      (false :: List.replicate 6 true)),5⟩ : Cfg) = _
  rw [hrep,hc]
  simp [init,List.append_assoc]

private theorem after_A (t v : Nat) :
    run (costA t v)
      (BB6.Agent32EAll.output (3*t+2) (3*v+1) []) =
        DRegularSource.sourceSection ⟨64*t+85+16*v,0,0⟩ := by
  rw [after_E]
  let k := kA t
  have hA := BB6.Agent32Code.full_A_code_implicit_nil k (code v)
  have hcost : costA t v =
      (12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) (code v) +
          (2*((4*k+3)+CryptidA.wordInc (code v))+6)) := rfl
  rw [hcost, hA]
  have hinc : CryptidA.wordInc (code v) = 8*v+13 :=
    inc_word v
  have hlen : 2*((4*k+3)+CryptidA.wordInc (code v))+5 =
      64*t+85+16*v := by
    rw [hinc]
    dsimp [k,kA]
    omega
  rw [hlen]
  have hf : List.replicate (64*t+85+16*v) true =
      true::true::List.replicate (64*t+83+16*v) true := by
    calc
      _ = List.replicate (2+(64*t+83+16*v)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+83+16*v) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hf]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (64*t+85+16*v)-2=64*t+83+16*v by omega]

/-- All exceptional E inputs with E-index 2 mod3 and q≡2 mod3
    have two source-certified returns to a canonical pure-unary F/0 section.
    The A close legitimately consumes the physically implicit final blank. -/
theorem every_two_mod_three_EA_rejoins (t v : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) (3*v+1) + costA t v)
        (DRegularSource.sourceSection ⟨9*t+10,3*v+2,1⟩))
      (DRegularSource.sourceSection ⟨64*t+85+16*v,0,0⟩) := by
  have hE : ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) (3*v+1))
        (DRegularSource.sourceSection ⟨9*t+10,3*v+2,1⟩))
      (BB6.Agent32EAll.output (3*t+2) (3*v+1) []) := by
    rw [start_E]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) (3*v+1)
  have hnext := source_congr (costA t v) hE
  rw [after_A] at hnext
  simpa only [run_add] using hnext

#print axioms every_two_mod_three_EA_rejoins
end BB6.EAResidueTwoSource
