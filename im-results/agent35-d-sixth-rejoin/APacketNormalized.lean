import Lean.Elab.Tactic.Omega
import APacketGeneral
import PacketNormalizer

set_option maxHeartbeats 20000000
set_option maxRecDepth 55000

namespace BB6.Agent35APacketNormalized
open CryptidBoundary
open BB6.Agent31PacketNormalizer
open BB6.Agent31PacketPaths

/-- Any finite maximal guarded B/E packet phase that terminates in the
    A residue with terminal unary block length congruent to 2 mod 3
    has an additional explicit original-machine return to a canonical
    regular F/0 section. The normalizer computes the path, its exact
    accumulated primitive time, and a checked source proof, for any
    starting packet and all three natural parameters. -/
theorem normalize_a_return (s : State) (k r : Nat)
    (ha : (normalize s).dst.a = 3*k+3)
    (hp : (normalize s).dst.p = 3*r+2) :
    run ((normalize s).cost +
      BB6.Agent35APacketGeneral.duration k (normalize s).dst.q r)
      (physical s BB6.Agent35APacketGeneral.ys) =
      DRegularSource.sourceSection
        ⟨8*k+11+2*(normalize s).dst.q+8*r,3,2⟩ := by
  rw [run_add, normalize_sound]
  change run
    (BB6.Agent35APacketGeneral.duration k (normalize s).dst.q r)
    (BB6.Agent31PacketSource.packet
      (normalize s).dst.a (normalize s).dst.q (normalize s).dst.p
      BB6.Agent35APacketGeneral.ys) = _
  rw [ha,hp]
  exact BB6.Agent35APacketGeneral.source_a_packet_regular
    k (normalize s).dst.q r

/-- Computationally checkable sufficient condition on the state obtained
    by the terminating packet normalizer. Every admissible output of the
    classifier is source certified by the previous theorem. -/
theorem normalize_a_return_mod (s : State)
    (ha : (normalize s).dst.a % 3 = 0)
    (ha3 : (normalize s).dst.a ≥ 3)
    (hp : (normalize s).dst.p % 3 = 2) :
    let k := ((normalize s).dst.a - 3)/3
    let r := ((normalize s).dst.p - 2)/3
    run ((normalize s).cost +
      BB6.Agent35APacketGeneral.duration k (normalize s).dst.q r)
      (physical s BB6.Agent35APacketGeneral.ys) =
    DRegularSource.sourceSection
      ⟨8*k+11+2*(normalize s).dst.q+8*r,3,2⟩ := by
  dsimp
  apply normalize_a_return s _ _
  · omega
  · omega

#print axioms normalize_a_return
#print axioms normalize_a_return_mod
end BB6.Agent35APacketNormalized
