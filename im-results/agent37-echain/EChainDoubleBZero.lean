import Lean.Elab.Tactic.Omega
import EChainBExit
import PacketP2ResetSource

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192

namespace BB6.Agent37EChainDoubleBZero

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset BB6.Agent2BoundaryBZero

def bZeroTime (k : Nat) : Nat := 12*k*k+49*k+40

def reset_k81_34_time (s Q : Nat) : Nat :=
  eTwoTime (81*s+34) Q +
    (chainTime 1 (54*s+23) 0 +
      (bTime (576*s+245) +
        (bTime (1536*s+656) + bZeroTime (4096*s+1752))))

/-- A second infinite changed-marker reset cylinder.  For k=81*s+34,
    the P2 reset is followed by one E-chain step, two ordinary B packets,
    and the arbitrary-tail B,q=0 return.  The result is the canonical
    regular section L(32768*s+2*Q+14028,3,2), for every s,Q≥0. -/
theorem reset_k81_34_regular (s Q : Nat) :
    run (reset_k81_34_time s Q)
      (packet (3*(81*s+34)+4) Q 2
        (false :: List.replicate 6 true)) =
      regularSection (32768*s+2*Q+14028) 3 2 := by
  let k := 81*s+34
  let h := 54*s+23
  let k1 := 576*s+245
  let k2 := 1536*s+656
  let k3 := 4096*s+1752
  let p := 2*Q+3
  have hmarker :
      BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
    decide
  have hprefix : 8*k+5 = 1+4*3*h := by
    dsimp [k,h]
    omega
  have hreset :
      run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false :: List.replicate 6 true)) =
      packet (1+4*3*h) 0 (2*Q+6) BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset, hprefix, hmarker]
  have hchain :
      run (chainTime 1 h 0)
        (packet (1+4*3*h) 0 (3+p) BB6.Agent35K4Shapes.marker) =
      packet (1+4*8*h) 2 p BB6.Agent35K4Shapes.marker := by
    simpa [chainTime] using
      (BB6.Agent37EChain.chain_return 1 h 0 p
        BB6.Agent35K4Shapes.marker (by dsimp [h]; omega))
  have ha1 : 1+4*8*h = 3*k1+2 := by
    dsimp [h,k1]
    omega
  have ha2 : 8*k1+10 = 3*k2+2 := by
    dsimp [k1,k2]
    omega
  have ha3 : 8*k2+10 = 3*k3+2 := by
    dsimp [k2,k3]
    omega
  have ha4 : 8*k3+9+p = 32768*s+2*Q+14028 := by
    dsimp [k3,p]
    omega
  have hb1 :
      run (bTime k1)
        (packet (3*k1+2) 2 p BB6.Agent35K4Shapes.marker) =
      packet (8*k1+10) 1 p BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet k1 1 p
      BB6.Agent35K4Shapes.marker
  have hb2 :
      run (bTime k2)
        (packet (3*k2+2) 1 p BB6.Agent35K4Shapes.marker) =
      packet (8*k2+10) 0 p BB6.Agent35K4Shapes.marker :=
    BB6.Agent31PacketSource.b_packet k2 0 p
      BB6.Agent35K4Shapes.marker
  have hmarkerTail :
      BB6.Agent35K4Shapes.marker = oppairs 3 ++ [true,true] := by decide
  have hb0 :
      run (bZeroTime k3)
        (packet (3*k3+2) 0 p BB6.Agent35K4Shapes.marker) =
      regularSection (8*k3+9+p) 3 2 := by
    dsimp [bZeroTime]
    rw [BB6.Agent2PacketP2Reset.b_zero_any, hmarkerTail]
    rfl
  unfold reset_k81_34_time
  rw [run_add, hreset]
  rw [run_add, hchain]
  rw [ha1]
  rw [run_add, hb1]
  rw [ha2]
  rw [run_add, hb2]
  rw [ha3]
  rw [hb0, ha4]

#print axioms reset_k81_34_regular

end BB6.Agent37EChainDoubleBZero
