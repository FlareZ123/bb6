import Lean.Elab.Tactic.Omega
import P2MarkerA
import PacketP2ResetSource

namespace BB6.Agent37P2K13
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

def firstK (s : Nat) := 81*s+13
def secondK (s : Nat) := 216*s+35
def thirdK (s : Nat) := 576*s+95
def fourthK (s : Nat) := 1536*s+255
def aK (s : Nat) := 4096*s+682

def eTime (k q : Nat) := 12*k*k+49*k+58+6*q

def beforeATime (s q : Nat) :=
  eTwoTime (firstK s) (q+2) +
    (eTime (secondK s) 0 +
      (eTime (thirdK s) 2 + eTime (fourthK s) 4))

/-- An unbounded residue class k=81s+13, q>=2 of the E,p=2 packet
    reset reaches the original source A class after four E endpoints. -/
theorem to_A (s q : Nat) :
    run (beforeATime s q)
      (packet (3*firstK s+4) (q+2) 2 (false::List.replicate 6 true)) =
      packet (3*aK s+3) 6 (2*q+1) BB6.Agent2PacketP2Reset.marker := by
  unfold beforeATime
  rw [run_add, e_two_reset]
  have h1 : 8*firstK s+5=3*secondK s+4 := by
    simp only [firstK,secondK]; omega
  have p1 : 2*(q+2)+6=(2*q+7)+3 := by omega
  rw [h1,p1]
  rw [run_add]
  have he1 :
      run (eTime (secondK s) 0)
        (packet (3*secondK s+4) 0 ((2*q+7)+3) BB6.Agent2PacketP2Reset.marker) =
      packet (8*secondK s+9) 2 (2*q+7) BB6.Agent2PacketP2Reset.marker := by
    simpa only [eTime,Nat.mul_zero,Nat.add_zero] using
      (e_packet (secondK s) 0 (2*q+7) BB6.Agent2PacketP2Reset.marker)
  rw [he1]
  have h2 : 8*secondK s+9=3*thirdK s+4 := by
    simp only [secondK,thirdK]; omega
  have p2 : 2*q+7=(2*q+4)+3 := by omega
  rw [h2,p2]
  rw [run_add]
  have he2 :
      run (eTime (thirdK s) 2)
        (packet (3*thirdK s+4) 2 ((2*q+4)+3) BB6.Agent2PacketP2Reset.marker) =
      packet (8*thirdK s+9) 4 (2*q+4) BB6.Agent2PacketP2Reset.marker := by
    simpa only [eTime] using
      (e_packet (thirdK s) 2 (2*q+4) BB6.Agent2PacketP2Reset.marker)
  rw [he2]
  have h3 : 8*thirdK s+9=3*fourthK s+4 := by
    simp only [thirdK,fourthK]; omega
  have p3 : 2*q+4=(2*q+1)+3 := by omega
  rw [h3,p3]
  have he3 :
      run (eTime (fourthK s) 4)
        (packet (3*fourthK s+4) 4 ((2*q+1)+3) BB6.Agent2PacketP2Reset.marker) =
      packet (8*fourthK s+9) 6 (2*q+1) BB6.Agent2PacketP2Reset.marker := by
    simpa only [eTime] using
      (e_packet (fourthK s) 4 (2*q+1) BB6.Agent2PacketP2Reset.marker)
  rw [he3]
  have h4 : 8*fourthK s+9=3*aK s+3 := by
    simp only [fourthK,aK]; omega
  rw [h4]

private theorem markers_eq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
  decide

/-- For each index k=81s+13 and q>=2, an authentic source-macro
    composition reaches a regular F/0 right-suffix shape. The three alternatives
    correspond to p modulo three and are all concrete unhalted endpoints. -/
theorem all_k13_q_ge2_regular (s q : Nat) :
    ∃ (T n : Nat),
      run T (packet (3*firstK s+4) (q+2) 2 (false::List.replicate 6 true)) =
          (⟨[],false,List.replicate n true ++
             [true,false,true,false,true,true,true],5⟩ : Cfg) ∨
      run T (packet (3*firstK s+4) (q+2) 2 (false::List.replicate 6 true)) =
          (⟨[],false,List.replicate n true,5⟩ : Cfg) ∨
      run T (packet (3*firstK s+4) (q+2) 2 (false::List.replicate 6 true)) =
          (⟨[],false,List.replicate n true ++
            [false,true,false,true,false,true,false,true,false],5⟩ : Cfg) := by
  obtain ⟨ta,n,h⟩ := BB6.Agent35MarkerA.all_A_marker_returns (aK s) 6 (2*q+1)
  refine ⟨beforeATime s q+ta,n,?_⟩
  rw [run_add,to_A,markers_eq]
  exact h

#print axioms to_A
#print axioms all_k13_q_ge2_regular
end BB6.Agent37P2K13
