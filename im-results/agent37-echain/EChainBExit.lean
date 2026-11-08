import Lean.Elab.Tactic.Omega
import EChainAExit
import EChainBResidues

namespace BB6.Agent37EChainBExit
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainResidues
open BB6.Agent37EChainAExit BB6.Agent37EChainBResidues
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

def bTime (kb : Nat) := 12*kb*kb+49*kb+40

private theorem markerEq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by decide

/-- A source-verified exact prefix can be precomposed with a regular endpoint. -/
theorem prepend (c d : Cfg) (t : Nat) (h : run t c = d)
    (hend : regularEndpoint d) : regularEndpoint c := by
  obtain ⟨tailTime,n,htail⟩ := hend
  unfold regularEndpoint
  refine ⟨t+tailTime,n,?_⟩
  rw [run_add,h]
  exact htail

/-- A guarded B call landing in A inherits Agent35's exact A-marker closure. -/
theorem B_to_A (kb ka qb p : Nat) (ha : 8*kb+10=3*ka+3) :
    regularEndpoint (packet (3*kb+2) (qb+1) p BB6.Agent35K4Shapes.marker) := by
  obtain ⟨ta,n,hret⟩ := BB6.Agent35MarkerA.all_A_marker_returns ka qb p
  unfold regularEndpoint
  refine ⟨bTime kb+ta,n,?_⟩
  dsimp only [bTime]
  rw [run_add,b_packet,ha]
  exact hret

/-- Arbitrarily many E returns followed by one B and one A completion. -/
theorem chain_B_to_A (d h kb ka q p : Nat)
    (hh : 1 ≤ h)
    (hq : 1 ≤ q+2*d)
    (hb : 1+4*8^d*h=3*kb+2)
    (ha : 8*kb+10=3*ka+3) :
    regularEndpoint
      (packet (1+4*3^d*h) q (3*d+p) BB6.Agent35K4Shapes.marker) := by
  have hqeq : q+2*d=(q+2*d-1)+1 := by omega
  have hBA : regularEndpoint
        (packet (1+4*8^d*h) (q+2*d) p BB6.Agent35K4Shapes.marker) := by
    rw [hb,hqeq]
    exact B_to_A kb ka (q+2*d-1) p ha
  exact prepend _ _ (chainTime d h q)
    (chain_return d h q p BB6.Agent35K4Shapes.marker hh) hBA

/-- Complete original-machine exceptional reset with d E calls then B and A. -/
theorem reset_B_to_A (d k h kb ka Q p : Nat)
    (hh : 1 ≤ h)
    (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (hb : 1+4*8^d*h=3*kb+2)
    (ha : 8*kb+10=3*ka+3)
    (hp : 2*Q+6=3*d+p) :
    regularEndpoint (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  have hBA := chain_B_to_A d h kb ka 0 p hh (by omega) hb ha
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5=4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by ac_rfl
  have hreset : run (eTwoTime k Q)
      (packet (3*k+4) Q 2 (false::List.replicate 6 true)) =
      packet (1+4*3^d*h) 0 (3*d+p) BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset,hprefix,hp,markerEq]
  exact prepend _ _ (eTwoTime k Q) hreset hBA

/-- Optimal pair budget for a B/A exit after d>=1 E packet calls. -/
theorem reset_B_to_A_resource (d k h kb ka Q : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (hb : 1+4*8^d*h=3*kb+2)
    (ha : 8*kb+10=3*ka+3)
    (hQ : 3*d ≤ 2*Q+6) :
    regularEndpoint (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  have hp : 2*Q+6=3*d+(2*Q+6-3*d) := by omega
  exact reset_B_to_A d k h kb ka Q (2*Q+6-3*d)
    hh hd hk hb ha hp

/-- Even-depth (d>=2) source B-then-A 3-adic reset cylinders. -/
theorem reset_even_depth_BA (n s Q : Nat) (hn : 1 ≤ n)
    (hQ : 3*(2*n) ≤ 2*Q+6) :
    regularEndpoint (packet (3*evenBK n s+4) Q 2 (false::List.replicate 6 true)) := by
  obtain ⟨kb,ka,hb,ha⟩ := even_BA_index n (2*s)
  have hv : 9*(2*s)+1=18*s+1 := by omega
  rw [hv] at hb
  exact reset_B_to_A_resource (2*n) (evenBK n s) (18*s+1) kb ka Q
    (by omega) (by omega) (evenBK_root n s) hb ha hQ

/-- Odd-depth (d>=1) source B-then-A 3-adic reset cylinders. -/
theorem reset_odd_depth_BA (n s Q : Nat)
    (hQ : 3*(2*n+1) ≤ 2*Q+6) :
    regularEndpoint (packet (3*oddBK n s+4) Q 2 (false::List.replicate 6 true)) := by
  obtain ⟨kb,ka,hb,ha⟩ := odd_BA_index n (2*s+1)
  have hv : 9*(2*s+1)+8=18*s+17 := by omega
  rw [hv] at hb
  exact reset_B_to_A_resource (2*n+1) (oddBK n s) (18*s+17) kb ka Q
    (by omega) (by omega) (oddBK_root n s) hb ha hQ

#print axioms prepend
#print axioms B_to_A
#print axioms chain_B_to_A
#print axioms reset_B_to_A
#print axioms reset_B_to_A_resource
#print axioms reset_even_depth_BA
#print axioms reset_odd_depth_BA
end BB6.Agent37EChainBExit
