import Lean.Elab.Tactic.Omega
import EChainBExit

namespace BB6.Agent37EChainDoubleBExit
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainAExit
open BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

/-- Two consecutive guarded B packets, for arbitrary untouched tail. -/
theorem b_twice (t q p : Nat) (ys : List Bool) :
    run (bTime (9*t+5)+bTime (24*t+16))
      (packet (27*t+17) (q+2) p ys) =
      packet (3*(64*t+45)+3) q p ys := by
  rw [run_add]
  have hb1 := b_packet (9*t+5) (q+1) p ys
  have h1 : 27*t+17=3*(9*t+5)+2 := by omega
  have h2 : 8*(9*t+5)+10=3*(24*t+16)+2 := by omega
  rw [h1, hb1, h2]
  have hb2 := b_packet (24*t+16) q p ys
  have h3 : 8*(24*t+16)+10=3*(64*t+45)+3 := by omega
  rw [hb2, h3]

/-- Two B operations, then an unrestricted A completion, to a regular F0. -/
theorem double_B_to_A (t q p : Nat) :
    regularEndpoint (packet (27*t+17) (q+2) p BB6.Agent35K4Shapes.marker) := by
  obtain ⟨ta,n,htail⟩ := BB6.Agent35MarkerA.all_A_marker_returns (64*t+45) q p
  unfold regularEndpoint
  refine ⟨bTime (9*t+5)+bTime (24*t+16)+ta,n,?_⟩
  rw [run_add,b_twice]
  exact htail

/-- Arbitrarily many E packets followed by exactly two B packets and A. -/
theorem chain_double_B_to_A (d h t q p : Nat) (hh : 1 ≤ h)
    (hd : 1 ≤ d)
    (ha : 1+4*8^d*h=27*t+17) :
    regularEndpoint
      (packet (1+4*3^d*h) q (3*d+p) BB6.Agent35K4Shapes.marker) := by
  have hq : 2 ≤ q+2*d := by omega
  have hqq : q+2*d=(q+2*d-2)+2 := by omega
  have hfinal : regularEndpoint
      (packet (1+4*8^d*h) (q+2*d) p BB6.Agent35K4Shapes.marker) := by
    rw [ha,hqq]
    exact double_B_to_A t (q+2*d-2) p
  exact prepend _ _ (chainTime d h q)
    (chain_return d h q p BB6.Agent35K4Shapes.marker hh) hfinal

/-- Reset source, arbitrary-depth E chain, two B packets, A completion. -/
theorem reset_double_B_to_A (d k h t Q : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=27*t+17)
    (hQ : 3*d ≤ 2*Q+6) :
    regularEndpoint (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  have hp : 2*Q+6=3*d+(2*Q+6-3*d) := by omega
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5=4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by ac_rfl
  have hm : BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by decide
  have hreset : run (eTwoTime k Q)
      (packet (3*k+4) Q 2 (false::List.replicate 6 true)) =
      packet (1+4*3^d*h) 0 (3*d+(2*Q+6-3*d)) BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset,hprefix,hp,hm]
  exact prepend _ _ (eTwoTime k Q) hreset
    (chain_double_B_to_A d h t 0 (2*Q+6-3*d) hh hd ha)

#print axioms b_twice
#print axioms double_B_to_A
#print axioms chain_double_B_to_A
#print axioms reset_double_B_to_A
end BB6.Agent37EChainDoubleBExit
