import Lean.Elab.Tactic.Omega
import EZeroMarkerP2Packet
import P2Residual146779Source

/-!
  New exact original-machine E/p2 Z-marker regularization at every
  E index k divisible by three, for all positive pair counts and
  all zero-marker depths.

  E/p2 first produces a B-index, exhausted q=0 packet with suffix
  0 1^(2m+6); B/q0 returns to the canonical regular F0 section
  L(a,1,2m+5).  Both source transitions preserve arbitrary implicit
  zero-padding via ObsEq.  No blank-start reachability assumed.
-/
namespace BB6.Agent36EZTwoBZero

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

/-- Genuine original-source two-macro exit for the full infinite
    E/p2 Z-marker family k=3t, q>0, all marker depths. -/
theorem e_two_Z_k0_regular (t q m : Nat) :
    ∃ T a pairsCount b,
      ObsEq
        (run T
          (packet (3*(3*t)+4) (q+1) 2
            (BB6.Agent2MarkerZero.marker m)))
        (regularSection a pairsCount b) := by
  let k : Nat := 3*t
  let kb : Nat := 8*t+1
  let te : Nat := 12*k*k+49*k+64+4*q+4*m
  let tb : Nat := 12*kb*kb+49*kb+40
  let a : Nat := 8*kb+9+(2*(q+1)+2)
  let mid : Cfg :=
    packet (3*kb+2) 0 (2*(q+1)+2)
      (false::List.replicate (2*m+6) true)
  have hi : 8*k+5=3*kb+2 := by dsimp [k,kb]; omega
  have he : ObsEq
      (run te
        (packet (3*k+4) (q+1) 2
          (BB6.Agent2MarkerZero.marker m))) mid := by
    have h := BB6.Agent26EZTwoPacket.e_two_Z_packet k q m
    rw [hi] at h
    simpa only [te,mid] using h
  have hr : run tb mid = regularSection a 1 (2*m+5) := by
    have hones : List.replicate (2*m+6) true =
        true :: List.replicate (2*m+5) true := by
      rw [show 2*m+6=(2*m+5)+1 by omega]
      simp [List.replicate_succ]
    dsimp [tb,mid,a]
    rw [BB6.Agent2PacketP2Reset.b_zero_any]
    simp [regularSection,oppairs,hones,List.append_assoc]
  refine ⟨te+tb,a,1,2*m+5,?_⟩
  change ObsEq
    (run (te+tb)
      (packet (3*k+4) (q+1) 2
        (BB6.Agent2MarkerZero.marker m)))
    (regularSection a 1 (2*m+5))
  exact source_chain te tb
    (packet (3*k+4) (q+1) 2
      (BB6.Agent2MarkerZero.marker m))
    mid (regularSection a 1 (2*m+5))
    he (by rw [hr]; exact BB6.Padding.cfgEq_refl _)

/-- Previously unresolved prepared source k=146779, Q=0, fixed-tail
    exception, fully original-machine resolved by exact guarded
    normalizer, two marker transformations, and the new E/p2 Z family.
    No genuine blank-root claim. -/
theorem k146779_original_regular :
    ∃ T a q b,
      ObsEq
        (run T
          (packet 440341 0 2
            (false :: List.replicate 6 true)))
        (regularSection a q b) := by
  obtain ⟨T0,h0⟩ :=
    BB6.Agent36Residual146779.residual_source
  have hk : 2879299338241 = 3*(3*319922148693)+4 := by decide
  have hq : 8=7+1 := by decide
  obtain ⟨T1,a,q,b,h1⟩ :=
    e_two_Z_k0_regular 319922148693 7 3
  refine ⟨T0+T1,a,q,b,?_⟩
  have h1' : ObsEq
      (run T1
        (packet 2879299338241 8 2
          (BB6.Agent2MarkerZero.marker 3)))
      (regularSection a q b) := by
    simpa only [←hk,←hq] using h1
  exact source_chain T0 T1
    (packet 440341 0 2
      (false::List.replicate 6 true))
    (packet 2879299338241 8 2
      (BB6.Agent2MarkerZero.marker 3))
    (regularSection a q b)
    (by rw [h0]; exact BB6.Padding.cfgEq_refl _) h1'

#print axioms e_two_Z_k0_regular
#print axioms k146779_original_regular
end BB6.Agent36EZTwoBZero
