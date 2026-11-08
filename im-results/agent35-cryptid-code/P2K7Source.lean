import Lean.Elab.Tactic.Omega
import PacketP2ResetSource
import P2K7ShapeCfg
import A1101010111Code
import CodeImplicitNil

namespace BB6.Agent35K7
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2PacketP2Reset
open BB6.Agent35K4Shapes (marker)
open BB6.Agent35K7Shapes (code codeTail)
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def firstK (t : Nat) := 27*t+25
def secondK (t : Nat) := 72*t+67
def thirdK (t : Nat) := 192*t+181
def aK (t : Nat) := 512*t+485

def e1Time (t : Nat) := 12*secondK t*secondK t+49*secondK t+58
def b2Time (t : Nat) := 12*thirdK t*thirdK t+49*thirdK t+40
def beforeATime (t q : Nat) := eTwoTime (firstK t) q + (e1Time t + b2Time t)

/-- Every k≡25 (mod27) exceptional reset reaches A by a full E-packet followed by B. -/
theorem to_A (t q : Nat) :
    run (beforeATime t q)
      (packet (3*firstK t+4) q 2 (false::List.replicate 6 true)) =
      packet (3*aK t+3) 1 (2*q+3) BB6.Agent2PacketP2Reset.marker := by
  unfold beforeATime
  rw [run_add, e_two_reset]
  have h1 : 8*firstK t+5=3*secondK t+4 := by
    simp only [firstK,secondK]
    omega
  have p1 : 2*q+6=(2*q+3)+3 := by omega
  rw [h1,p1]
  rw [run_add]
  have he1 := e_packet (secondK t) 0 (2*q+3) BB6.Agent2PacketP2Reset.marker
  have he1' : run (e1Time t)
      (packet (3*secondK t+4) 0 ((2*q+3)+3) BB6.Agent2PacketP2Reset.marker) =
      packet (8*secondK t+9) 2 (2*q+3) BB6.Agent2PacketP2Reset.marker := by
    simpa only [e1Time,Nat.mul_zero,Nat.add_zero] using he1
  rw [he1']
  have h2 : 8*secondK t+9=3*thirdK t+2 := by
    simp only [secondK,thirdK]
    omega
  rw [h2]
  have hb := b_packet (thirdK t) 1 (2*q+3) BB6.Agent2PacketP2Reset.marker
  have hb' : run (b2Time t)
      (packet (3*thirdK t+2) (1+1) (2*q+3) BB6.Agent2PacketP2Reset.marker) =
      packet (8*thirdK t+10) 1 (2*q+3) BB6.Agent2PacketP2Reset.marker := by
    simpa only [b2Time] using hb
  rw [hb']
  have h3 : 8*thirdK t+10=3*aK t+3 := by
    simp only [thirdK,aK]
    omega
  rw [h3]

/-- Source-original completion with suffix parameter q divisible by three. -/
theorem close_zero (t u : Nat) :
    let ka := aK t
    let ws := code u
    let finalTime := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost (4*ka+3) ws +
        (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    run (beforeATime t (3*u)+finalTime)
      (packet (3*firstK t+4) (3*u) 2 (false::List.replicate 6 true)) =
    (⟨[],false,
      List.replicate (2*((4*ka+3)+CryptidA.wordInc ws)+5) true ++
        [true,false,true,false,true,true,true],5⟩ : Cfg) := by
  dsimp only
  rw [run_add,to_A]
  change run _ (packet (3*(512*t+485)+3) 1 (2*(3*u)+3) BB6.Agent35K4Shapes.marker) = _
  rw [shape_zero]
  exact BB6.Agent35.full_A_code (aK t) (code u)
    [true,false,true,false,true,true,true]

/-- Source-original completion with suffix parameter q≡1 mod3. -/
theorem close_one (t u : Nat) :
    let ka := aK t
    let ws := code u
    let m := 4*ka+3+CryptidA.wordInc ws
    let finalTime := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost (4*ka+3) ws + (2*m+36))
    run (beforeATime t (3*u+1)+finalTime)
      (packet (3*firstK t+4) (3*u+1) 2 (false::List.replicate 6 true)) =
    (⟨[],false,List.replicate (2*m+5) true ++
      [false,true,false,true,false,true,false,true,false],5⟩ : Cfg) := by
  dsimp only
  rw [run_add,to_A]
  change run _ (packet (3*(512*t+485)+3) 1 (2*(3*u+1)+3) BB6.Agent35K4Shapes.marker) = _
  rw [shape_one]
  exact BB6.Agent26ACode.full_A_code_1101010111 (aK t) (code u) []

/-- Source-original completion for q≡2 mod3; implicit right blank respected. -/
theorem close_two (t u : Nat) :
    let ka := aK t
    let ws := codeTail u
    let finalTime := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost (4*ka+3) ws +
        (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    run (beforeATime t (3*u+2)+finalTime)
      (packet (3*firstK t+4) (3*u+2) 2 (false::List.replicate 6 true)) =
    (⟨[],false,List.replicate
      (2*((4*ka+3)+CryptidA.wordInc ws)+5) true,5⟩ : Cfg) := by
  dsimp only
  rw [run_add,to_A]
  change run _ (packet (3*(512*t+485)+3) 1 (2*(3*u+2)+3) BB6.Agent35K4Shapes.marker) = _
  rw [shape_two]
  exact BB6.Agent32Code.full_A_code_implicit_nil (aK t) (codeTail u)

#print axioms to_A
#print axioms close_zero
#print axioms close_one
#print axioms close_two
end BB6.Agent35K7
