import Lean.Elab.Tactic.Omega
import EChainDoubleBExit

namespace BB6.Agent37EChainBEExit
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37EChain BB6.Agent37EChainAExit
open BB6.Agent37EChainBExit
open BB6.Agent2PacketP2Reset

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

private theorem markerEq :
    BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
  decide

/-- One B edge followed by one E edge.  The E edge is available precisely
    when the B successor has A-index residue 1 mod 3.  The suffix is untouched. -/
theorem b_then_e (kb ke qb p : Nat) (ys : List Bool)
    (he : 8*kb+10=3*ke+4) :
    run (bTime kb + eTime ke qb)
      (packet (3*kb+2) (qb+1) (3+p) ys) =
      packet (8*ke+9) (qb+2) p ys := by
  rw [run_add]
  dsimp only [bTime, eTime]
  rw [b_packet, he]
  have hp : 3+p=p+3 := by omega
  rw [hp, e_packet]

/-- A complete B -> E -> A corridor after an arbitrary-depth E prefix.
    The proof isolates the source path from the later residue parameterization.
    The congruence 1+4*8^d*h = 27*t+20 is the exact B-to-E residue
    cylinder.  The resource is three additional 1s for the B-successor E edge. -/
theorem chain_B_E_A (d h t q p : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (ha : 1+4*8^d*h=27*t+20) :
    regularEndpoint
      (packet (1+4*3^d*h) q (3*d+(3+p))
        BB6.Agent35K4Shapes.marker) := by
  let kb : Nat := 9*t+6
  let ke : Nat := 24*t+18
  let ka : Nat := 64*t+50
  have hb : 1+4*8^d*h=3*kb+2 := by
    calc
      1+4*8^d*h = 27*t+20 := ha
      _ = 3*kb+2 := by dsimp [kb]; omega
  have he : 8*kb+10=3*ke+4 := by
    dsimp [kb,ke]
    omega
  have hA : 8*ke+9=3*ka+3 := by
    dsimp [ke,ka]
    omega
  have hq : (q+2*d-1)+1=q+2*d := by omega
  have hq2 : (q+2*d-1)+2=q+2*d+1 := by omega
  have hfirst :
      run (chainTime d h q)
        (packet (1+4*3^d*h) q (3*d+(3+p))
          BB6.Agent35K4Shapes.marker) =
      packet (3*kb+2) (q+2*d) (3+p)
        BB6.Agent35K4Shapes.marker := by
    rw [chain_return d h q (3+p) BB6.Agent35K4Shapes.marker hh, hb]
  have hBE0 := b_then_e kb ke (q+2*d-1) p
    BB6.Agent35K4Shapes.marker he
  have hBE :
      run (bTime kb + eTime ke (q+2*d-1))
        (packet (3*kb+2) (q+2*d) (3+p)
          BB6.Agent35K4Shapes.marker) =
      packet (8*ke+9) (q+2*d+1) p
        BB6.Agent35K4Shapes.marker := by
    simpa only [hq, hq2] using hBE0
  obtain ⟨ta,n,htail⟩ :=
    BB6.Agent35MarkerA.all_A_marker_returns ka (q+2*d+1) p
  have hfinal :
      regularEndpoint
        (packet (8*ke+9) (q+2*d+1) p
          BB6.Agent35K4Shapes.marker) := by
    rw [hA]
    unfold regularEndpoint
    exact ⟨ta,n,htail⟩
  have hmid :
      regularEndpoint
        (packet (3*kb+2) (q+2*d) (3+p)
          BB6.Agent35K4Shapes.marker) :=
    prepend _ _ (bTime kb + eTime ke (q+2*d-1)) hBE hfinal
  exact prepend _ _ (chainTime d h q) hfirst hmid

/-- Compose the B -> E -> A corridor with the original-source E,p=2 reset.
    This is a new infinite family of fixed-tail p=2 packets returning to L. -/
theorem reset_B_E_A (d k h t Q p : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=27*t+20)
    (hp : 2*Q+6=3*d+(3+p)) :
    regularEndpoint
      (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  have hprefix : 8*k+5=1+4*3^d*h := by
    calc
      8*k+5 = 4*(2*k+1)+1 := by omega
      _ = 4*(3^d*h)+1 := by rw [hk]
      _ = 1+4*3^d*h := by ac_rfl
  have hreset :
      run (eTwoTime k Q)
        (packet (3*k+4) Q 2 (false::List.replicate 6 true)) =
      packet (1+4*3^d*h) 0 (3*d+(3+p))
        BB6.Agent35K4Shapes.marker := by
    rw [e_two_reset, hprefix, hp, markerEq]
  exact prepend _ _ (eTwoTime k Q) hreset
    (chain_B_E_A d h t 0 p hh hd ha)

/-- Resource-guarded form: the initial p=2 reset supplies enough ones
    for d E edges, one B-successor E edge, and no further suffix use. -/
theorem reset_B_E_A_resource (d k h t Q : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (ha : 1+4*8^d*h=27*t+20)
    (hQ : 3*d+3 ≤ 2*Q+6) :
    regularEndpoint
      (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  let p : Nat := 2*Q+6-(3*d+3)
  have hp : 2*Q+6=3*d+(3+p) := by
    dsimp [p]
    omega
  exact reset_B_E_A d k h t Q p hh hd hk ha hp

/-- Explicit residue-cylinder form.  For fixed d, the congruence
    (1+4*8^d*h) mod 27 = 20 determines t and hence the B -> E -> A
    corridor. -/
theorem reset_B_E_A_mod27 (d k h Q : Nat)
    (hh : 1 ≤ h) (hd : 1 ≤ d)
    (hk : 2*k+1=3^d*h)
    (hmod : (1+4*8^d*h) % 27 = 20)
    (hQ : 3*d+3 ≤ 2*Q+6) :
    regularEndpoint
      (packet (3*k+4) Q 2 (false::List.replicate 6 true)) := by
  let n : Nat := 1+4*8^d*h
  let t : Nat := n/27
  have hnmod : n%27=20 := by simpa [n] using hmod
  have hn : n=27*t+20 := by
    dsimp [t]
    omega
  have ha : 1+4*8^d*h=27*t+20 := by
    simpa [n] using hn
  exact reset_B_E_A_resource d k h t Q hh hd hk ha hQ

#print axioms b_then_e
#print axioms chain_B_E_A
#print axioms reset_B_E_A
#print axioms reset_B_E_A_resource
#print axioms reset_B_E_A_mod27
end BB6.Agent37EChainBEExit
