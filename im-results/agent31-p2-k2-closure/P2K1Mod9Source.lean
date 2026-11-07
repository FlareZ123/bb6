import Lean.Elab.Tactic.Omega
import P2K2Source
import P2K1Mod9Shapes

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

namespace BB6.Agent31P2K1Mod9Source
open CryptidBoundary BB6.Agent31PacketSource BB6.Agent2PacketP2Reset
open BB6.Agent31P2K1Mod9 BB6.BoundaryPadding

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

/-- Source-derived E,p=2 reset followed by guarded E with q=0. -/
theorem after_two (s q : Nat) :
    let k := 9*s+1
    let j := 24*s+3
    run (eTwoTime k q+(12*j*j+49*j+58))
      (packet (3*k+4) q 2 (false::List.replicate 6 true)) =
      packet (8*j+9) 2 (2*q+3) BB6.Agent2PacketP2Reset.marker := by
  dsimp only
  rw [run_add,e_two_reset]
  have ha : 8*(9*s+1)+5=3*(24*s+3)+4 := by omega
  have hp : 2*q+6=(2*q+3)+3 := by omega
  rw [ha,hp]
  simpa only [Nat.zero_mul,Nat.add_zero,Nat.zero_add] using
    (BB6.Agent31PacketSource.e_packet (24*s+3) 0 (2*q+3) BB6.Agent2PacketP2Reset.marker)

private theorem shape_zero (s u : Nat) :
  packet (8*(24*s+3)+9) 2 (2*(3*u)+3) BB6.Agent2PacketP2Reset.marker =
  init (List.replicate (3*(64*s+10)+1) true ++ false ::
    (CryptidA.wordCode (code (2*u+1)) ++
     (false :: [true,false,true,false,true,true,true]))) := by
  have hn : 8*(24*s+3)+9=2+(3*(64*s+10)+1) := by omega
  have hw := word_zero u
  rw [←sourceCode] at hw
  change (⟨[],false,List.replicate (8*(24*s+3)+9) true ++
     (false :: ([true,false,true,false] ++
        (List.replicate (2*(3*u)+3) true ++ BB6.Agent2PacketP2Reset.marker))),5⟩ : Cfg) = _
  rw [show BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker by rfl]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem shape_one (s u : Nat) :
  packet (8*(24*s+3)+9) 2 (2*(3*u+1)+3) BB6.Agent2PacketP2Reset.marker =
  init (List.replicate (3*(64*s+10)+1) true ++ false ::
    (CryptidA.wordCode (code (2*u+1)) ++
      BB6.Agent26ACode.packet [])) := by
  have hn : 8*(24*s+3)+9=2+(3*(64*s+10)+1) := by omega
  have hw := word_one u
  rw [←sourceCode] at hw
  change (⟨[],false,List.replicate (8*(24*s+3)+9) true ++
     (false :: ([true,false,true,false] ++
        (List.replicate (2*(3*u+1)+3) true ++ BB6.Agent2PacketP2Reset.marker))),5⟩ : Cfg) = _
  rw [show BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker by rfl]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

private theorem shape_two (s u : Nat) :
  packet (8*(24*s+3)+9) 2 (2*(3*u+2)+3) BB6.Agent2PacketP2Reset.marker =
  init (List.replicate (3*(64*s+10)+1) true ++ false ::
    CryptidA.wordCode (codeTail (2*u+2))) := by
  have hn : 8*(24*s+3)+9=2+(3*(64*s+10)+1) := by omega
  have hw := word_two u
  rw [←sourceCode] at hw
  change (⟨[],false,List.replicate (8*(24*s+3)+9) true ++
     (false :: ([true,false,true,false] ++
        (List.replicate (2*(3*u+2)+3) true ++ BB6.Agent2PacketP2Reset.marker))),5⟩ : Cfg) = _
  rw [show BB6.Agent2PacketP2Reset.marker = BB6.Agent31P2K2.marker by rfl]
  rw [hw,hn]
  rw [←List.replicate_append_replicate]
  rfl

/-- Three macro endpoints in original source, first q residue. -/
theorem three_return_zero (s u : Nat) :
    let ka := 64*s+10
    let ws := code (2*u+1)
    let aTime := (12*ka*ka+41*ka+32)+
     (CryptidA.wordCost (4*ka+3) ws +
       (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    let eTime := eTwoTime (9*s+1) (3*u) +
       (12*(24*s+3)*(24*s+3)+49*(24*s+3)+58)
    run (eTime+aTime)
      (packet (27*s+7) (3*u) 2 (false::List.replicate 6 true)) =
      ⟨[],false,List.replicate
        (2*(4*ka+3+CryptidA.wordInc ws)+5) true ++
          [true,false,true,false,true,true,true],5⟩ := by
  dsimp only
  rw [show 27*s+7=3*(9*s+1)+4 by omega]
  rw [run_add,after_two,shape_zero]
  exact BB6.Agent35.full_A_code (64*s+10) (code (2*u+1))
    [true,false,true,false,true,true,true]

theorem three_return_one (s u : Nat) :
    let ka := 64*s+10
    let ws := code (2*u+1)
    let m := 4*ka+3+CryptidA.wordInc ws
    let aTime := (12*ka*ka+41*ka+32)+
       (CryptidA.wordCost (4*ka+3) ws + (2*m+36))
    let eTime := eTwoTime (9*s+1) (3*u+1) +
       (12*(24*s+3)*(24*s+3)+49*(24*s+3)+58)
    run (eTime+aTime)
      (packet (27*s+7) (3*u+1) 2 (false::List.replicate 6 true)) =
      ⟨[],false,List.replicate (2*m+5) true ++
        BB6.Agent26ACode.tail [],5⟩ := by
  dsimp only
  rw [show 27*s+7=3*(9*s+1)+4 by omega]
  rw [run_add,after_two,shape_one]
  exact BB6.Agent26ACode.full_A_code_1101010111 (64*s+10) (code (2*u+1)) []

theorem three_return_two_physical (s u : Nat) :
    let ka := 64*s+10
    let ws := codeTail (2*u+2)
    let xs := List.replicate (3*ka+1) true ++ false :: CryptidA.wordCode ws
    let aTime := (12*ka*ka+41*ka+32)+
       (CryptidA.wordCost (4*ka+3) ws +
         (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    let eTime := eTwoTime (9*s+1) (3*u+2) +
       (12*(24*s+3)*(24*s+3)+49*(24*s+3)+58)
    ObsEq (run (eTime+aTime)
      (packet (27*s+7) (3*u+2) 2 (false::List.replicate 6 true)))
      ⟨[],false,List.replicate (2*(4*ka+3+CryptidA.wordInc ws)+5) true,5⟩ := by
  dsimp only
  rw [show 27*s+7=3*(9*s+1)+4 by omega]
  rw [run_add,after_two,shape_two]
  let ws : List Bool := codeTail (2*u+2)
  let xs : List Bool := List.replicate (3*(64*s+10)+1) true ++ false :: CryptidA.wordCode ws
  have hpad := source_init_pad
    ((12*(64*s+10)*(64*s+10)+41*(64*s+10)+32)+
       (CryptidA.wordCost (4*(64*s+10)+3) ws +
         (2*((4*(64*s+10)+3)+CryptidA.wordInc ws)+6))) 1 xs
  have hpadded :
    run ((12*(64*s+10)*(64*s+10)+41*(64*s+10)+32)+
       (CryptidA.wordCost (4*(64*s+10)+3) ws +
         (2*((4*(64*s+10)+3)+CryptidA.wordInc ws)+6)))
      (init (xs ++ List.replicate 1 false)) =
      ⟨[],false,List.replicate (2*(4*(64*s+10)+3+CryptidA.wordInc ws)+5) true,5⟩ := by
    have hshape : xs ++ List.replicate 1 false =
      List.replicate (3*(64*s+10)+1) true ++ false ::
        (CryptidA.wordCode ws ++ (false::[])) := by
      simp [xs,List.append_assoc]
    rw [hshape]
    simpa only [List.append_nil] using (BB6.Agent35.full_A_code (64*s+10) ws [])
  rw [hpadded] at hpad
  exact hpad

#print axioms after_two
#print axioms three_return_zero
#print axioms three_return_one
#print axioms three_return_two_physical
end BB6.Agent31P2K1Mod9Source
