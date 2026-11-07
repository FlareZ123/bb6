import Lean.Elab.Tactic.Omega
import PacketNormalizeSource
import AOnePacketBoundarySource
import BoundaryBZero

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

namespace BB6.Agent2PacketOneReentry

open CryptidBoundary BB6.Agent31PacketRank BB6.Agent31PacketPaths
open BB6.Agent31PacketSource BB6.Agent2PacketNormalizeSource
open BB6.BoundaryPadding BB6.Padding

def fixedTail : List Bool := false :: List.replicate 6 true

/-- Every source-valid terminal B/E packet with the fixed last word,
    or an A terminal with p=1 mod3, reaches a literal regular L section.
    The target includes a pure unary section as q=b=0. -/
theorem one_terminal_regular (d : BB6.Agent31PacketRank.Packet)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 1)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a q b,
      ObsEq (run T (packet d.a d.q d.p fixedTail))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  rcases hc with hA | hB | hE
  · let k : Nat := (d.a-3)/3
    let r : Nat := (d.p-1)/3
    have ha' : d.a = 3*k+3 := by
      dsimp [k]
      omega
    have hp' : d.p = 3*r+1 := by
      dsimp [r]
      omega
    refine ⟨BB6.Agent2AOneBoundary.aCost k d.q r,
      BB6.Agent2AOneBoundary.aUnary k d.q r,0,0,?_⟩
    have h := BB6.Agent2AOneBoundary.a_p1_boundary k d.q r
    simpa [ha',hp',fixedTail,BB6.Agent2BoundaryBZero.regularSection]
      using h
  · obtain ⟨hB,hq⟩ := hB
    let k : Nat := (d.a-2)/3
    have ha' : d.a = 3*k+2 := by
      dsimp [k]
      omega
    refine ⟨12*k*k+49*k+40,8*k+9+d.p,1,5,?_⟩
    have h := BB6.Agent2BoundaryBZero.b_zero_source k d.p
    simpa [ha',hq,fixedTail] using
      (show ObsEq
        (run (12*k*k+49*k+40)
          (packet (3*k+2) 0 d.p (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection (8*k+9+d.p) 1 5) by
        rw [h]
        exact BB6.Padding.cfgEq_refl _)
  · obtain ⟨hE,hpSmall⟩ := hE
    have hp1 : d.p=1 := by omega
    refine ⟨0,d.a,d.q+2,5,?_⟩
    change ObsEq (packet d.a d.q d.p fixedTail)
      (BB6.Agent2BoundaryBZero.regularSection d.a (d.q+2) 5)
    rw [hp1]
    rw [show fixedTail = false :: List.replicate 6 true by rfl]
    rw [BB6.Agent2BoundaryBZero.e_one_regular]
    exact BB6.Padding.cfgEq_refl _

/-- Source-certified unbounded physical reentry: every a≥4 B/E packet
    with fixed right suffix 0 1^6 and initial p ≡ 1 (mod 3) reaches
    some regular L(a,q,b) section after finitely many actual primitive
    original D Turing-machine steps. No closedness of subsequent orbits
    is claimed, and this theorem has no implication of global nonhalting. -/
theorem all_one_packets_regular (c : BB6.Agent31PacketRank.Packet)
    (ha : c.a ≥ 4) (hp : c.p % 3 = 1) :
    ∃ T a q b,
      ObsEq (run T (packet c.a c.q c.p fixedTail))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let d : BB6.Agent31PacketRank.Packet :=
    (BB6.Agent31PacketRank.normalizeWithCount c).2
  obtain ⟨T,hraw⟩ :=
    BB6.Agent2PacketNormalizeSource.normalized_original_source c ha fixedTail
  have hb : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q=0) ∨
      (d.a % 3 = 1 ∧ (d.p=0 ∨ d.p=1)) :=
    BB6.Agent2PacketSafe.normalize_safe_exit c ha (by omega)
  have hamin : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
  have hpmod : d.p%3=1 := by
    have h := BB6.Agent2PacketSafe.normalize_pmod c
    omega
  obtain ⟨n,a,q,b,hboundary⟩ :=
    one_terminal_regular d hamin hpmod hb
  refine ⟨T+n,a,q,b,?_⟩
  have hfirst : ObsEq
      (run T (packet c.a c.q c.p fixedTail))
      (packet d.a d.q d.p fixedTail) := by
    change run T (packet c.a c.q c.p fixedTail) =
      packet d.a d.q d.p fixedTail at hraw
    rw [hraw]
    exact BB6.Padding.cfgEq_refl _
  exact source_chain T n
    (packet c.a c.q c.p fixedTail)
    (packet d.a d.q d.p fixedTail)
    (BB6.Agent2BoundaryBZero.regularSection a q b)
    hfirst hboundary

#print axioms one_terminal_regular
#print axioms all_one_packets_regular

end BB6.Agent2PacketOneReentry
