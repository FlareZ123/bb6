import Lean.Elab.Tactic.Omega
import PacketP2ResetSource
import P2K4ShapeCfg
import A1101010111Code
import CodeImplicitNil

namespace BB6.Agent35K4
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2PacketP2Reset
open BB6.Agent35K4Shapes
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def firstK (t : Nat) := 27*t+22
def secondK (t : Nat) := 72*t+59
def thirdK (t : Nat) := 192*t+159
def aK (t : Nat) := 512*t+426

def e1Time (t : Nat) := 12*secondK t*secondK t+49*secondK t+58
def e2Time (t : Nat) := 12*thirdK t*thirdK t+49*thirdK t+58+6*2
def twoEsTime (t q : Nat) := eTwoTime (firstK t) q + (e1Time t + e2Time t)

/-- Every k≡22 (mod 27) reset enters an A section after two more E sections.
All three source returns retain the exact original six-state transition times. -/
theorem two_es (t q : Nat) :
    run (twoEsTime t q)
      (packet (3*firstK t+4) q 2 (false::List.replicate 6 true)) =
      packet (3*aK t+3) 4 (2*q) BB6.Agent2PacketP2Reset.marker := by
  unfold twoEsTime
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
  have h2 : 8*secondK t+9=3*thirdK t+4 := by
    simp only [secondK,thirdK]
    omega
  rw [h2]
  have he2 := e_packet (thirdK t) 2 (2*q) BB6.Agent2PacketP2Reset.marker
  have he2' : run (e2Time t)
      (packet (3*thirdK t+4) 2 ((2*q)+3) BB6.Agent2PacketP2Reset.marker) =
      packet (8*thirdK t+9) 4 (2*q) BB6.Agent2PacketP2Reset.marker := by
    simpa only [e2Time] using he2
  rw [he2']
  have h3 : 8*thirdK t+9=3*aK t+3 := by
    simp only [thirdK,aK]
    omega
  rw [h3]

/-- Exact source endpoint for q≡0 modulo 3; the residual word is regular (01)^2 11. -/
theorem close_zero (t u : Nat) :
    let ka := aK t
    let ws := code u
    let finalTime := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost (4*ka+3) ws +
        (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    run (twoEsTime t (3*u)+finalTime)
      (packet (3*firstK t+4) (3*u) 2 (false::List.replicate 6 true)) =
    (⟨[],false,
      List.replicate (2*((4*ka+3)+CryptidA.wordInc ws)+5) true ++
        [true,false,true,false,true,true,true],5⟩ : Cfg) := by
  dsimp only
  rw [run_add,two_es]
  change run _ (packet (3*(512*t+426)+3) 4 (2*(3*u)) BB6.Agent35K4Shapes.marker) = _
  rw [shape_zero]
  exact BB6.Agent35.full_A_code (aK t) (code u)
    [true,false,true,false,true,true,true]

/-- Exact source endpoint for q≡1 modulo 3, with an explicit trailing blank zero. -/
theorem close_one (t u : Nat) :
    let ka := aK t
    let ws := code u
    let m := 4*ka+3+CryptidA.wordInc ws
    let finalTime := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost (4*ka+3) ws + (2*m+36))
    run (twoEsTime t (3*u+1)+finalTime)
      (packet (3*firstK t+4) (3*u+1) 2 (false::List.replicate 6 true)) =
    (⟨[],false,List.replicate (2*m+5) true ++
      [false,true,false,true,false,true,false,true,false],5⟩ : Cfg) := by
  dsimp only
  rw [run_add,two_es]
  change run _ (packet (3*(512*t+426)+3) 4 (2*(3*u+1)) BB6.Agent35K4Shapes.marker) = _
  rw [shape_one]
  exact BB6.Agent26ACode.full_A_code_1101010111
    (aK t) (code u) []

/-- Exact source endpoint for q≡2 modulo 3 using the original implicit blank, no fabricated tape cell. -/
theorem close_two (t u : Nat) :
    let ka := aK t
    let ws := codeTail u
    let finalTime := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost (4*ka+3) ws +
        (2*((4*ka+3)+CryptidA.wordInc ws)+6))
    run (twoEsTime t (3*u+2)+finalTime)
      (packet (3*firstK t+4) (3*u+2) 2 (false::List.replicate 6 true)) =
    (⟨[],false,List.replicate
      (2*((4*ka+3)+CryptidA.wordInc ws)+5) true,5⟩ : Cfg) := by
  dsimp only
  rw [run_add,two_es]
  change run _ (packet (3*(512*t+426)+3) 4 (2*(3*u+2)) BB6.Agent35K4Shapes.marker) = _
  rw [shape_two]
  exact BB6.Agent32Code.full_A_code_implicit_nil
    (aK t) (codeTail u)

#print axioms two_es
#print axioms close_zero
#print axioms close_one
#print axioms close_two
end BB6.Agent35K4
