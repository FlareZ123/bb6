import Lean.Elab.Tactic.Omega
import EAResidueTwoSource
import A110111

set_option maxHeartbeats 35000000
set_option maxRecDepth 8192

namespace BB6.EAResidueOneSource
open CryptidBoundary BB6.BoundaryPadding

private def code (v : Nat) : List Bool :=
  List.replicate (2*(v+1)) true
private def kA (t : Nat) := 8*t+6
private def packet (ys : List Bool) : List Bool :=
  [true,true,false,true,true,true] ++ ys
private def costA (t v : Nat) :=
  (12*(kA t)*(kA t)+41*(kA t)+32) +
    (CryptidA.wordCost (4*(kA t)+3) (code v) +
      (2*((4*(kA t)+3)+CryptidA.wordInc (code v))+24))

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

private theorem code_inc (n : Nat) :
    CryptidA.wordInc (List.replicate n true) = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 4 + CryptidA.wordInc (List.replicate n true) = 4*(n+1)
    rw [ih]
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
    DRegularSource.sourceSection ⟨9*t+10,3*v+4,1⟩ =
      init (List.replicate (3*(3*t+2)+2) true ++
        (false :: (pairs (3*v+3) ++ [true,true]))) := by
  have hn : (9*t+10)-2=3*(3*t+2)+2 := by omega
  have hword : oppairs (3*v+4) ++ List.replicate 1 true =
      false :: (pairs (3*v+3) ++ [true,true]) := by
    simpa only [List.replicate_one,
      show (3*v+3)+1=3*v+4 by omega] using
      (oppairs_to_pairs (3*v+3))
  simp only [DRegularSource.sourceSection, hn, List.replicate_one]
  rw [List.append_assoc, hword]

private theorem after_E (t v : Nat) :
    BB6.Agent32EAll.output (3*t+2) (3*v+3) [] =
      init (List.replicate (3*(kA t)+1) true ++
        (false :: (CryptidA.wordCode (code v) ++
           packet (List.replicate 3 true)))) := by
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
      List.replicate (6*v+6) true := by
    rw [code,code_ones]
    congr 1
    omega
  change (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
    (false :: List.replicate (2*(3*v+3)+2) true ++
      (false :: List.replicate 6 true)),5⟩ : Cfg) = _
  rw [hrep,hc]
  have hrepl : List.replicate (2*(3*v+3)+2) true =
      List.replicate (6*v+6) true ++ [true,true] := by
    calc
      _ = List.replicate ((6*v+6)+2) true := by congr 1; omega
      _ = List.replicate (6*v+6) true ++
          List.replicate 2 true := (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hrepl]
  simp [init,packet,List.append_assoc]

private theorem raw_after_A (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    run ((12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) ws + (2*m+24)))
      (init (List.replicate (3*k+1) true ++
          (false :: (CryptidA.wordCode ws ++ packet ys)))) =
        ⟨[],false,List.replicate (2*m+5) true ++
          (false::true::false::true::false::ys),5⟩ := by
  dsimp
  rw [run_add,prefix_A,run_add]
  change run (2*(4*k+3+CryptidA.wordInc ws)+24)
    (run (CryptidA.wordCost (4*k+3) ws)
      (BB6.Agent35.aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ packet ys))) = _
  rw [BB6.Agent35.a_code_return]
  change run (2*(4*k+3+CryptidA.wordInc ws)+24)
    (BB6.Agent35.aBoundary (4*k+3+CryptidA.wordInc ws) (packet ys)) = _
  rw [show (BB6.Agent35.aBoundary (4*k+3+CryptidA.wordInc ws)
      (packet ys)) =
        CryptidBoundary.aBoundary ((4*k+CryptidA.wordInc ws)+3)
          (true::true::false::true::true::true::ys) by
            simp [BB6.Agent35.aBoundary,CryptidBoundary.aBoundary,packet,
              List.append_assoc]]
  have htime : 2*(4*k+3+CryptidA.wordInc ws)+24 =
      2*((4*k+CryptidA.wordInc ws)+3)+24 := by omega
  rw [htime, CryptidBoundary.a110111_run]
  rfl

private theorem after_A (t v : Nat) :
    run (costA t v)
      (BB6.Agent32EAll.output (3*t+2) (3*v+3) []) =
        DRegularSource.sourceSection ⟨64*t+75+16*v,3,2⟩ := by
  rw [after_E]
  let k := kA t
  have hc : costA t v =
      (12*k*k+41*k+32) +
        (CryptidA.wordCost (4*k+3) (code v) +
          (2*(4*k+3+CryptidA.wordInc (code v))+24)) := rfl
  rw [hc]
  have hA := raw_after_A k (code v) (List.replicate 3 true)
  dsimp at hA
  rw [hA]
  have hinc : CryptidA.wordInc (code v) = 8*(v+1) := by
    rw [code,code_inc]
  have hlen : 2*(4*k+3+CryptidA.wordInc (code v))+5 =
      64*t+75+16*v := by
    rw [hinc]
    dsimp [k,kA]
    omega
  rw [hlen]
  have hf : List.replicate (64*t+75+16*v) true =
      true::true::List.replicate (64*t+73+16*v) true := by
    calc
      _ = List.replicate (2+(64*t+73+16*v)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (64*t+73+16*v) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hf]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (64*t+75+16*v)-2=64*t+73+16*v by omega]

/-- Exceptional E-index k≡2 (mod3), with q≡1(mod3) and q≥4.
    Two original source returns reach regular output (q=3,b=2).
    Uses a universal A-code prefix and the certified A-110111 suffix. -/
theorem every_one_mod_three_EA_rejoins (t v : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) (3*v+3) + costA t v)
        (DRegularSource.sourceSection ⟨9*t+10,3*v+4,1⟩))
      (DRegularSource.sourceSection ⟨64*t+75+16*v,3,2⟩) := by
  have hE : ObsEq
      (run (BB6.Agent32EAll.duration (3*t+2) (3*v+3))
        (DRegularSource.sourceSection ⟨9*t+10,3*v+4,1⟩))
      (BB6.Agent32EAll.output (3*t+2) (3*v+3) []) := by
    rw [start_E]
    exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+2) (3*v+3)
  have hnext := source_congr (costA t v) hE
  rw [after_A] at hnext
  simpa only [run_add] using hnext

#print axioms every_one_mod_three_EA_rejoins
end BB6.EAResidueOneSource
