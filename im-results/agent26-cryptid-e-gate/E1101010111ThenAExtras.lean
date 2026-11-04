import Lean.Elab.Tactic.Omega
import E1101010111ThenA
import A110101Closure

namespace BB6.Agent26EThenAExtras

open CryptidBoundary
open BB6.Agent26E1101010111
open BB6.Agent26EThenB
open BB6.Agent26EThenA

set_option maxHeartbeats 15000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def aTenWord (ys : List Bool) : List Bool :=
  [true,true,false,true,false,true,false,true,false,true,false,false] ++ ys

/-- The new first-return A boundary for q=3u+1 requires an explicit
    terminal zero in the original E input. -/
theorem e_to_a_ten_section (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      bWord (3*u+1) (false::ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (List.replicate (2*u+2) true) ++
        aTenWord ys)) := by
  rw [bWord_shape,tripleCode]
  have hcount : 2*(3*u+1)+6 = 3*(2*u+2)+2 := by omega
  rw [hcount]
  have htwos :
      List.replicate (3*(2*u+2)+2) true =
      List.replicate (3*(2*u+2)) true ++ [true,true] := by
    rw [show 3*(2*u+2)+2 = (3*(2*u+2))+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  rw [htwos]
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn, ←List.replicate_append_replicate]
    rfl
  rw [hrep]
  simp [aTenWord,tail,init,List.append_assoc]

/-- Universal original-machine mixed-code A terminal with a final 110101010100
    word. All source steps and finite right tails remain exact. -/
theorem full_A_code_ten (k : Nat) (ws ys : List Bool) :
    let m := 4*k+3+CryptidA.wordInc ws
    run ((12*k*k+41*k+32) +
      (CryptidA.wordCost (4*k+3) ws + (2*m+32)))
      (init (List.replicate (3*k+1) true ++
        false :: (CryptidA.wordCode ws ++ aTenWord ys))) =
      ⟨[],false,List.replicate (2*m+1) true ++
        (false :: List.replicate 14 true ++ ys),5⟩ := by
  dsimp
  let m := 4*k+3+CryptidA.wordInc ws
  rw [run_add,prefix_A]
  change run (CryptidA.wordCost (4*k+3) ws + (2*m+32))
    (BB6.Agent35.aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ aTenWord ys)) = _
  rw [run_add, BB6.Agent35.a_code_return]
  change run (2*m+32)
    (aBoundary m (aTenWord ys)) = _
  have hm : m=(m-1)+1 := by dsimp [m]; omega
  have ht : 2*m+32=2*(m-1)+34 := by dsimp [m]; omega
  rw [ht]
  conv_lhs => arg 2; rw [hm]
  change run (2*(m-1)+34)
    (aBoundary ((m-1)+1) (aTenWord ys)) = _
  have hr := a_ten_return (m-1) ys
  have hn : 2*(m-1)+3=2*m+1 := by dsimp [m]; omega
  rw [hn] at hr
  exact hr

/-- New E->A q=3u+1 direct source connection. -/
theorem e_then_a_ten (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let m := 4*ka+3+CryptidA.wordInc ws
    let eTime := 12*ke*ke+49*ke+80+4*(3*u+1)
    let aTime := (12*ka*ka+41*ka+32)+
      (CryptidA.wordCost (4*ka+3) ws+(2*m+32))
    run (eTime+aTime)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs (3*u+1) ++ wordE (false::ys)))) =
      ⟨[],false,List.replicate (2*m+1) true ++
        (false :: List.replicate 14 true ++ ys),5⟩ := by
  dsimp
  rw [run_add,full_E_1101010111_pairs (3*t+2) (3*u+1) (false::ys)]
  rw [e_to_a_ten_section]
  exact full_A_code_ten (8*t+6) (List.replicate (2*u+2) true) ys

/-- 111 token repetition followed by five 10 tokens. -/
theorem triple_then_five_code (r : Nat) :
    CryptidA.wordCode
      (List.replicate r true ++ List.replicate 5 false) =
      List.replicate (3*r) true ++ pairs 5 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ([true,true,true] ++
        CryptidA.wordCode (List.replicate r true ++
          List.replicate 5 false)) =
      List.replicate (3*(r+1)) true ++ pairs 5
    rw [ih]
    have ht : 3*(r+1)=3+3*r := by omega
    rw [ht, ←List.replicate_append_replicate]
    simp [List.append_assoc]

/-- The q=3u+2 E output enters the general code-on-zero A closure. -/
theorem e_to_a_five_section (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      bWord (3*u+2) (false::ys),5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode
        (List.replicate (2*u+3) true ++ List.replicate 5 false) ++
        (false::ys))) := by
  rw [bWord_shape,triple_then_five_code]
  have hcount : 2*(3*u+2)+6=3*(2*u+3)+1 := by omega
  rw [hcount]
  have hlast : List.replicate (3*(2*u+3)+1) true =
      List.replicate (3*(2*u+3)) true ++ [true] := by
    rw [show 3*(2*u+3)+1=(3*(2*u+3))+1 by omega,
      ←List.replicate_append_replicate]
    rfl
  rw [hlast]
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn, ←List.replicate_append_replicate]
    rfl
  rw [hrep]
  simp [tail,pairs,init,List.append_assoc]

/-- New E->A q=3u+2 source return.  Explicit zero delimiter is preserved. -/
theorem e_then_a_five (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let ka := 8*t+6
    let ws := List.replicate (2*u+3) true ++ List.replicate 5 false
    let m := 4*ka+3+CryptidA.wordInc ws
    let eTime := 12*ke*ke+49*ke+80+4*(3*u+2)
    let aTime := (12*ka*ka+41*ka+32)+
      (CryptidA.wordCost (4*ka+3) ws+(2*m+6))
    run (eTime+aTime)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs (3*u+2) ++ wordE (false::ys)))) =
      ⟨[],false,List.replicate (2*m+5) true ++ ys,5⟩ := by
  dsimp
  rw [run_add,full_E_1101010111_pairs (3*t+2) (3*u+2) (false::ys)]
  rw [e_to_a_five_section]
  exact BB6.Agent35.full_A_code (8*t+6)
    (List.replicate (2*u+3) true ++ List.replicate 5 false) ys

#print axioms e_to_a_ten_section
#print axioms full_A_code_ten
#print axioms e_then_a_ten
#print axioms triple_then_five_code
#print axioms e_to_a_five_section
#print axioms e_then_a_five

end BB6.Agent26EThenAExtras
