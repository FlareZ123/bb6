import Lean.Elab.Tactic.Omega
import PacketOneReentry
import PacketZeroBoundarySource

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

namespace BB6.Agent2PacketSafeReentry

open CryptidBoundary BB6.Agent31PacketRank
open BB6.Agent31PacketSource BB6.Agent2PacketNormalizeSource
open BB6.BoundaryPadding BB6.Padding

/-- Remaining safe terminal residue: p=0 mod3, with A/E p=0 handled
    by actual original-source closing macros; B q=0 handled by full_B. -/
theorem zero_terminal_regular (d : BB6.Agent31PacketRank.Packet)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 0)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a q b,
      ObsEq
        (run T
          (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  rcases hc with hA | hB | hE
  · let k : Nat := (d.a-3)/3
    let r : Nat := d.p/3
    have ha' : d.a = 3*k+3 := by
      dsimp [k]
      omega
    have hp' : d.p = 3*r := by
      dsimp [r]
      omega
    refine ⟨BB6.Agent2PacketZeroBoundary.aZeroCost k d.q r,
      BB6.Agent2PacketZeroBoundary.aZeroUnary k d.q r,0,0,?_⟩
    have h := BB6.Agent2PacketZeroBoundary.a_zero_boundary k d.q r
    simpa [ha',hp',BB6.Agent2PacketOneReentry.fixedTail,
      BB6.Agent2BoundaryBZero.regularSection,oppairs]
      using
        (show ObsEq
          (run (BB6.Agent2PacketZeroBoundary.aZeroCost k d.q r)
            (packet (3*k+3) d.q (3*r) (false::List.replicate 6 true)))
          (⟨[],false,List.replicate
            (BB6.Agent2PacketZeroBoundary.aZeroUnary k d.q r) true,5⟩) by
          rw [h]
          exact BB6.Padding.cfgEq_refl _)
  · obtain ⟨hB,hq⟩ := hB
    let k : Nat := (d.a-2)/3
    have ha' : d.a = 3*k+2 := by
      dsimp [k]
      omega
    refine ⟨12*k*k+49*k+40,8*k+9+d.p,1,5,?_⟩
    have h := BB6.Agent2BoundaryBZero.b_zero_source k d.p
    simpa [ha',hq,BB6.Agent2PacketOneReentry.fixedTail] using
      (show ObsEq
        (run (12*k*k+49*k+40)
          (packet (3*k+2) 0 d.p (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection (8*k+9+d.p) 1 5) by
        rw [h]
        exact BB6.Padding.cfgEq_refl _)
  · obtain ⟨hE,hpSmall⟩ := hE
    have hp0 : d.p=0 := by omega
    let k : Nat := (d.a-4)/3
    have ha' : d.a=3*k+4 := by
      dsimp [k]
      omega
    refine ⟨12*k*k+49*k+50+4*d.q,8*k+5,1,2*d.q+11,?_⟩
    have h := BB6.Agent2PacketZeroBoundary.e_zero_boundary k d.q
    simpa [ha',hp0,BB6.Agent2PacketOneReentry.fixedTail] using
      (show ObsEq
        (run (12*k*k+49*k+50+4*d.q)
          (packet (3*k+4) d.q 0 (false::List.replicate 6 true)))
        (BB6.Agent2BoundaryBZero.regularSection (8*k+5) 1 (2*d.q+11)) by
        rw [h]
        exact BB6.Padding.cfgEq_refl _)

/-- Universal p=0 mod3 subgrammar reaches a canonical regular source
    section after finitely many genuine raw source transitions. -/
theorem all_zero_packets_regular (c : BB6.Agent31PacketRank.Packet)
    (ha : c.a ≥ 4) (hp : c.p % 3 = 0) :
    ∃ T a q b,
      ObsEq
        (run T
          (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  let d : BB6.Agent31PacketRank.Packet :=
    (BB6.Agent31PacketRank.normalizeWithCount c).2
  obtain ⟨T,hraw⟩ :=
    BB6.Agent2PacketNormalizeSource.normalized_original_source c ha
      BB6.Agent2PacketOneReentry.fixedTail
  have hb : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q=0) ∨
      (d.a % 3 = 1 ∧ (d.p=0 ∨ d.p=1)) :=
    BB6.Agent2PacketSafe.normalize_safe_exit c ha (by omega)
  have hamin : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
  have hpmod : d.p % 3=0 :=
    (BB6.Agent2PacketSafe.normalize_pmod c).trans hp
  obtain ⟨n,a,q,b,hboundary⟩ :=
    zero_terminal_regular d hamin hpmod hb
  refine ⟨T+n,a,q,b,?_⟩
  have hfirst : ObsEq
      (run T (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail))
      (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail) := by
    change run T
      (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail) =
      packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail at hraw
    rw [hraw]
    exact BB6.Padding.cfgEq_refl _
  exact source_chain T n
    (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail)
    (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail)
    (BB6.Agent2BoundaryBZero.regularSection a q b)
    hfirst hboundary

/-- Main fixed-tail closure for the entire safe residue class p≠2 mod3.
    The original six-state machine, from ANY source-valid packet M with
    suffix 0 1^6 and p=0 or 1 (mod3), reaches the regular section
    language in finite primitive time. No true-blank global closure follows. -/
theorem all_safe_packets_regular (c : BB6.Agent31PacketRank.Packet)
    (ha : c.a ≥ 4) (hp : c.p % 3 ≠ 2) :
    ∃ T a q b,
      ObsEq
        (run T
          (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail))
        (BB6.Agent2BoundaryBZero.regularSection a q b) := by
  by_cases hzero : c.p%3=0
  · exact all_zero_packets_regular c ha hzero
  · have hone : c.p%3=1 := by omega
    exact BB6.Agent2PacketOneReentry.all_one_packets_regular c ha hone

#print axioms zero_terminal_regular
#print axioms all_zero_packets_regular
#print axioms all_safe_packets_regular

end BB6.Agent2PacketSafeReentry
