import Lean.Elab.Tactic.Omega
import PacketP2ResetSource
import A1101010111Code
import BoundaryPadding
import P2K2Shapes

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

namespace BB6.Agent31P2K2Source

open CryptidBoundary BB6.Agent31PacketSource BB6.Agent2PacketP2Reset
open BB6.Agent31P2K2 BB6.BoundaryPadding

private theorem sourceCode (ws : List Bool) :
    CryptidA.wordCode ws = BB6.Agent31P2K2.wordCode ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih => cases b <;> simp [CryptidA.wordCode,BB6.Agent31P2K2.wordCode,ih]

private theorem sourceInc (ws : List Bool) :
    CryptidA.wordInc ws = BB6.Agent31P2K2.wordInc ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih => cases b <;> simp [CryptidA.wordInc,BB6.Agent31P2K2.wordInc,ih]

private theorem sourceCost (m : Nat) (ws : List Bool) :
    CryptidA.wordCost m ws = BB6.Agent31P2K2.wordCost m ws := by
  induction ws generalizing m with
  | nil => rfl
  | cons b ws ih =>
    cases b
    · change 2+CryptidA.wordCost (m+1) ws = 2+BB6.Agent31P2K2.wordCost (m+1) ws
      rw [ih]
    · change 6*m+41+CryptidA.wordCost (m+4) ws = 6*m+41+BB6.Agent31P2K2.wordCost (m+4) ws
      rw [ih]

/-- Source-correspondent polynomial cost checks. -/
theorem source_poly_zero (t u : Nat) :
    eTwoTime (3*t+2) (3*u) +
      ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32) +
        (CryptidA.wordCost (4*(8*t+6)+3) (List.replicate (2*u+2) true) +
        (2*(4*(8*t+6)+3+CryptidA.wordInc (List.replicate (2*u+2) true))+6))) =
      876*t*t+384*t*u+2219*t+48*u*u+506*u+1430 := by
  have h := total_cost_zero t u
  dsimp only at h
  rw [←sourceCost,←sourceInc] at h
  simpa only [eTwoTime] using h

theorem source_poly_one (t u : Nat) :
    eTwoTime (3*t+2) (3*u+1) +
      ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32) +
        (CryptidA.wordCost (4*(8*t+6)+3) (List.replicate (2*u+2) true) +
        (2*(4*(8*t+6)+3+CryptidA.wordInc (List.replicate (2*u+2) true))+36))) =
      876*t*t+384*t*u+2219*t+48*u*u+506*u+1464 := by
  have h := total_cost_one t u
  dsimp only at h
  rw [←sourceCost,←sourceInc] at h
  simpa only [eTwoTime] using h

theorem source_poly_two (t u : Nat) :
    let ws := List.replicate (2*u+3) true ++ [false,false,false,true]
    eTwoTime (3*t+2) (3*u+2) +
      ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32) +
        (CryptidA.wordCost (4*(8*t+6)+3) ws +
        (2*(4*(8*t+6)+3+CryptidA.wordInc ws)+6))) =
      876*t*t+384*t*u+2603*t+48*u*u+602*u+2010 := by
  have h := total_cost_two t u
  dsimp only at h ⊢
  rw [←sourceCost,←sourceInc] at h
  simpa only [eTwoTime] using h

private theorem markerEq : BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker := by
  rfl

private theorem one_tail (t u : Nat) :
  packet (8*(3*t+2)+5) 0 (2*(3*u+1)+6) BB6.Agent2PacketP2Reset.marker =
  init (List.replicate (3*(8*t+6)+1) true ++ false ::
    (CryptidA.wordCode (List.replicate (2*u+2) true) ++
     BB6.Agent26ACode.packet [])) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hw := residue_one_word u
  rw [←sourceCode] at hw
  rw [markerEq]
  simp only [BB6.Agent31PacketSource.packet,word,oppairs,init,
     List.nil_append,BB6.Agent26ACode.packet,List.append_nil]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem zero_tail (t u : Nat) :
  packet (8*(3*t+2)+5) 0 (2*(3*u)+6) BB6.Agent2PacketP2Reset.marker =
  init (List.replicate (3*(8*t+6)+1) true ++ false ::
    (CryptidA.wordCode (List.replicate (2*u+2) true) ++
     (false :: [true,false,true,false,true,true,true]))) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hw := residue_zero_word u
  rw [←sourceCode] at hw
  rw [markerEq]
  simp only [BB6.Agent31PacketSource.packet,word,oppairs,init,
     List.nil_append]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem two_tail (t u : Nat) :
  packet (8*(3*t+2)+5) 0 (2*(3*u+2)+6) BB6.Agent2PacketP2Reset.marker =
  init (List.replicate (3*(8*t+6)+1) true ++ false ::
    CryptidA.wordCode (List.replicate (2*u+3) true ++ [false,false,false,true])) := by
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hw := residue_two_word u
  rw [←sourceCode] at hw
  rw [markerEq]
  simp only [BB6.Agent31PacketSource.packet,word,oppairs,init,
     List.nil_append]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem start_eq (t : Nat) :
    9*t+10 = 3*(3*t+2)+4 := by omega

/-- Complete q≡0 return branch for original source, with exact primitive time. -/
theorem two_return_zero (t u : Nat) :
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let aTime := (12*ka*ka+41*ka+32) +
       (CryptidA.wordCost (4*ka+3) ws +
        (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    run (eTwoTime (3*t+2) (3*u) + aTime)
      (packet (9*t+10) (3*u) 2 (false::List.replicate 6 true)) =
      ⟨[],false,
       List.replicate (2*((4*ka+3)+CryptidA.wordInc ws)+5) true ++
          [true,false,true,false,true,true,true],5⟩ := by
  dsimp only
  rw [start_eq]
  rw [run_add, e_two_reset]
  rw [zero_tail]
  exact BB6.Agent35.full_A_code (8*t+6) (List.replicate (2*u+2) true)
    [true,false,true,false,true,true,true]

/-- Complete q≡1 original-source return via 1101010111 A terminal. -/
theorem two_return_one (t u : Nat) :
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let m := 4*ka+3+CryptidA.wordInc ws
    let aTime := (12*ka*ka+41*ka+32) +
       (CryptidA.wordCost (4*ka+3) ws + (2*m+36))
    run (eTwoTime (3*t+2) (3*u+1)+aTime)
      (packet (9*t+10) (3*u+1) 2 (false::List.replicate 6 true)) =
      ⟨[],false,List.replicate (2*m+5) true ++
         BB6.Agent26ACode.tail [],5⟩ := by
  dsimp only
  rw [start_eq]
  rw [run_add,e_two_reset]
  rw [one_tail]
  exact BB6.Agent26ACode.full_A_code_1101010111 (8*t+6)
    (List.replicate (2*u+2) true) []

/-- Complete q≡2 branch modulo physical right-blank observational equivalence. -/
theorem two_return_two_physical (t u : Nat) :
    let ka := 8*t+6
    let ws := List.replicate (2*u+3) true ++ [false,false,false,true]
    let xs := List.replicate (3*ka+1) true ++ false :: CryptidA.wordCode ws
    let aTime := (12*ka*ka+41*ka+32)+
      (CryptidA.wordCost (4*ka+3) ws +
        (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    ObsEq (run (eTwoTime (3*t+2) (3*u+2)+aTime)
      (packet (9*t+10) (3*u+2) 2 (false::List.replicate 6 true)))
      ⟨[],false,
        List.replicate (2*((4*ka+3)+CryptidA.wordInc ws)+5) true,5⟩ := by
  dsimp only
  rw [start_eq]
  rw [run_add,e_two_reset,two_tail]
  let ws : List Bool := List.replicate (2*u+3) true ++ [false,false,false,true]
  let xs : List Bool := List.replicate (3*(8*t+6)+1) true ++ false :: CryptidA.wordCode ws
  have hpad := source_init_pad
    ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32)+
      (CryptidA.wordCost (4*(8*t+6)+3) ws +
       (2*((4*(8*t+6)+3)+CryptidA.wordInc ws)+6))) 1 xs
  have hpadded :
    run ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32)+
      (CryptidA.wordCost (4*(8*t+6)+3) ws +
       (2*((4*(8*t+6)+3)+CryptidA.wordInc ws)+6)))
      (init (xs ++ List.replicate 1 false)) =
      ⟨[],false,List.replicate
          (2*((4*(8*t+6)+3)+CryptidA.wordInc ws)+5) true,5⟩ := by
    have hshape : xs ++ List.replicate 1 false =
        List.replicate (3*(8*t+6)+1) true ++
          false :: (CryptidA.wordCode ws ++ (false::[])) := by
      simp [xs,List.append_assoc]
    rw [hshape]
    simpa only [List.append_nil] using (BB6.Agent35.full_A_code (8*t+6) ws [])
  rw [hpadded] at hpad
  exact hpad

#print axioms source_poly_zero
#print axioms source_poly_one
#print axioms source_poly_two
#print axioms two_return_zero
#print axioms two_return_one
#print axioms two_return_two_physical
end BB6.Agent31P2K2Source
