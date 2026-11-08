import Lean.Elab.Tactic.Omega
import EChainSource
import EChainResidues
import P2MarkerA

namespace BB6.Agent37EChainAExit
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainResidues
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 15000000
set_option maxRecDepth 8192

/-- A designated F/0 endpoint is regular in one of the three exact grammar forms. -/
def regularEndpoint (c : Cfg) : Prop :=
  ∃ (T n : Nat),
    run T c = (⟨[],false,List.replicate n true ++
      [true,false,true,false,true,true,true],5⟩ : Cfg) ∨
    run T c = (⟨[],false,List.replicate n true,5⟩ : Cfg) ∨
    run T c = (⟨[],false,List.replicate n true ++
      [false,true,false,true,false,true,false,true,false],5⟩ : Cfg)

private theorem markers_eq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by decide

/-- Every arbitrary-depth E chain whose final unary index is in the A
    congruence class closes into a regular original F/0 section. -/
theorem all_depth_A (d h ka q p : Nat)
    (hh : 1 ≤ h) (ha : 1+4*8^d*h=3*ka+3) :
    regularEndpoint
      (packet (1+4*3^d*h) q (3*d+p) BB6.Agent35K4Shapes.marker) := by
  obtain ⟨tailTime,n,htail⟩ := BB6.Agent35MarkerA.all_A_marker_returns ka (q+2*d) p
  unfold regularEndpoint
  refine ⟨chainTime d h q+tailTime,n,?_⟩
  rw [run_add,chain_return d h q p BB6.Agent35K4Shapes.marker hh,ha]
  exact htail

/-- Full original-machine E,p=2 reset followed by d E returns and A closure. -/
theorem reset_A (d k h ka Q p : Nat)
    (hh : 1 ≤ h)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=3*ka+3)
    (hp : 2*Q+6=3*d+p) :
    regularEndpoint (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  obtain ⟨tailTime,n,htail⟩ := all_depth_A d h ka 0 p hh ha
  unfold regularEndpoint
  refine ⟨eTwoTime k Q+tailTime,n,?_⟩
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5=4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by ac_rfl
  rw [run_add,e_two_reset,hprefix,hp,markers_eq]
  exact htail

/-- The optimal linear resource guard for the entire E-only phase. -/
theorem reset_A_resource (d k h ka Q : Nat)
    (hh : 1 ≤ h)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=3*ka+3)
    (hQ : 3*d ≤ 2*Q+6) :
    regularEndpoint (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  have hp : 2*Q+6=3*d+(2*Q+6-3*d) := by omega
  exact reset_A d k h ka Q (2*Q+6-3*d) hh hk ha hp

/-- Even-depth A-exit cylinders; includes k=3s+2, k=27s+22,
    k=243s+202, and every later even-depth class. -/
theorem reset_even_depth (n s Q : Nat) (hQ : 3*(2*n) ≤ 2*Q+6) :
    regularEndpoint (packet (3*evenK n s+4) Q 2 (false::List.replicate 6 true)) := by
  obtain ⟨ka,ha⟩ := even_A_index n (2*s+1)
  have hv : 3*(2*s+1)+2=6*s+5 := by omega
  rw [hv] at ha
  exact reset_A_resource (2*n) (evenK n s) (6*s+5) ka Q
    (by omega) (evenK_root n s) ha hQ

/-- Odd-depth A-exit cylinders; includes k=9s+1, k=81s+13,
    k=729s+121, and every later odd-depth class. -/
theorem reset_odd_depth (n s Q : Nat) (hQ : 3*(2*n+1) ≤ 2*Q+6) :
    regularEndpoint (packet (3*oddK n s+4) Q 2 (false::List.replicate 6 true)) := by
  obtain ⟨ka,ha⟩ := odd_A_index n (2*s)
  have hv : 3*(2*s)+1=6*s+1 := by omega
  rw [hv] at ha
  exact reset_A_resource (2*n+1) (oddK n s) (6*s+1) ka Q
    (by omega) (oddK_root n s) ha hQ

#print axioms all_depth_A
#print axioms reset_A
#print axioms reset_A_resource
#print axioms reset_even_depth
#print axioms reset_odd_depth
end BB6.Agent37EChainAExit
