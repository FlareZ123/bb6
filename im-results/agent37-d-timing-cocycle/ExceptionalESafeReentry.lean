import Lean.Elab.Tactic.Omega
import EExceptionalShift
import PacketSafeReentry

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace BB6.Agent37ExceptionalESafeReentry

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

/-- The first original-source E return from L(3*k+4,q,1), q>=2,
    is exactly the fixed-tail packet M(8*k+5,0,2*q; 0 1^6). -/
private theorem e_output_packet (k q : Nat) (hq : 2 ≤ q) :
    BB6.Agent32EAll.output k (q-1) [] =
      packet (8*k+5) 0 (2*q)
        BB6.Agent2PacketOneReentry.fixedTail := by
  cases q with
  | zero => omega
  | succ q =>
    cases q with
    | zero => omega
    | succ r =>
      have hp : 2*(r+1)+2 = 2*(r+2) := by omega
      simp [BB6.Agent32EAll.output, packet, word,
        BB6.Agent2PacketOneReentry.fixedTail,
        CryptidBoundary.oppairs, hp]

/-- Every regular E-exit with q>=2 and q not congruent to 1 mod 3
    returns to the regular section language in finite primitive time.
    This is uniform in the unary parameter k; it generalizes the
    a=9*t+10 safe subfamily by composing EAllDouble with PacketSafeReentry. -/
theorem all_E_safe_reentry (k q : Nat) (hq : 2 ≤ q)
    (hclass : q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (run (BB6.Agent32EAll.duration k (q-1) + T)
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
  let c : BB6.Agent31PacketRank.Packet := ⟨8*k+5,0,2*q⟩
  have hq1 : 1 ≤ q := by omega
  have hE0 := BB6.EExceptionalShift.e_source k (q-1)
  have hE1 :
      ObsEq
        (run (BB6.Agent32EAll.duration k (q-1))
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent32EAll.output k (q-1) []) := by
    simpa only [Nat.sub_add_cancel hq1] using hE0
  have hshape := e_output_packet k q hq
  have hE :
      ObsEq
        (run (BB6.Agent32EAll.duration k (q-1))
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (packet c.a c.q c.p
          BB6.Agent2PacketOneReentry.fixedTail) := by
    rw [hshape] at hE1
    simpa [c] using hE1
  have ha : c.a ≥ 4 := by
    dsimp [c]
    omega
  have hp : c.p % 3 ≠ 2 := by
    dsimp [c]
    omega
  obtain ⟨T,a,q',b,hpacket⟩ :=
    BB6.Agent2PacketSafeReentry.all_safe_packets_regular c ha hp
  exact ⟨T,a,q',b,
    source_chain (BB6.Agent32EAll.duration k (q-1)) T
      (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
      (packet c.a c.q c.p
        BB6.Agent2PacketOneReentry.fixedTail)
      (BB6.Agent2BoundaryBZero.regularSection a q' b)
      hE hpacket⟩

#print axioms all_E_safe_reentry

end BB6.Agent37ExceptionalESafeReentry
