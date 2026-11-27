import Lean.Elab.Tactic.Omega
import EExceptionalShift
import PacketSafeReentry
import DRegularSourceShift

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace BB6.Agent37ExceptionalESafeCanonical

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

/-- Exact EAllDouble output shape for the fixed-tail safe-E family. -/
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

private theorem regularSection_sourceSection (a q b : Nat)
    (ha : 2 ≤ a) :
    BB6.Agent2BoundaryBZero.regularSection a q b =
      DRegularSource.sourceSection ⟨a,q,b⟩ := by
  simp only [BB6.Agent2BoundaryBZero.regularSection,
    DRegularSource.sourceSection, CryptidBoundary.init]
  have hrepAdd (m n : Nat) :
      List.replicate (m+n) true =
        List.replicate m true ++ List.replicate n true := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show Nat.succ m + n = (m+n)+1 by omega]
      rw [List.replicate_succ]
      rw [ih]
      rw [←List.cons_append]
      rw [←List.replicate_succ]
  have hrep : List.replicate a true =
      [true,true] ++ List.replicate (a-2) true := by
    rw [show a = 2+(a-2) by omega, hrepAdd]
    simp
  rw [hrep]
  simp [List.append_assoc]

private theorem canon_zero_q (a : Nat) (ha : 2 ≤ a) :
    DRegular.Canon ⟨a,0,0⟩ := by
  constructor
  · exact ha
  · exact Or.inr rfl

private theorem canon_nonzero_q (a q b : Nat)
    (ha : 2 ≤ a) (hq : q ≠ 0) :
    DRegular.Canon ⟨a,q,b⟩ := by
  constructor
  · exact ha
  · exact Or.inl hq

/-- Canonical source-section form of the p=0 mod 3 safe terminal cases.
    The explicit endpoint floors are retained instead of hidden inside
    the regular-section existential. -/
theorem zero_terminal_regular_canonical
    (d : BB6.Agent31PacketRank.Packet)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 0)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a q b,
      ObsEq
        (run T (packet d.a d.q d.p
          BB6.Agent2PacketOneReentry.fixedTail))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  rcases hc with hA | hB | hE
  · let k : Nat := (d.a-3)/3
    let r : Nat := d.p/3
    have ha' : d.a = 3*k+3 := by dsimp [k]; omega
    have hp' : d.p = 3*r := by dsimp [r]; omega
    let a : Nat := BB6.Agent2PacketZeroBoundary.aZeroUnary k d.q r
    have hfloor : 2 ≤ a := by
      dsimp [a,BB6.Agent2PacketZeroBoundary.aZeroUnary]
      omega
    refine ⟨BB6.Agent2PacketZeroBoundary.aZeroCost k d.q r,
      a,0,0,?_,canon_zero_q a hfloor⟩
    have h := BB6.Agent2PacketZeroBoundary.a_zero_boundary k d.q r
    have hreg :
        run (BB6.Agent2PacketZeroBoundary.aZeroCost k d.q r)
          (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail) =
        BB6.Agent2BoundaryBZero.regularSection a 0 0 := by
      simpa [a,ha',hp',BB6.Agent2PacketOneReentry.fixedTail,
        BB6.Agent2BoundaryBZero.regularSection,oppairs] using h
    rw [hreg,regularSection_sourceSection a 0 0 hfloor]
    exact BB6.Padding.cfgEq_refl _
  · obtain ⟨hB,hq⟩ := hB
    let k : Nat := (d.a-2)/3
    have ha' : d.a = 3*k+2 := by dsimp [k]; omega
    let a : Nat := 8*k+9+d.p
    have hfloor : 2 ≤ a := by dsimp [a]; omega
    refine ⟨12*k*k+49*k+40,a,1,5,?_,
      canon_nonzero_q a 1 5 hfloor (by decide)⟩
    have h := BB6.Agent2BoundaryBZero.b_zero_source k d.p
    have hreg :
        ObsEq
          (run (12*k*k+49*k+40)
            (packet d.a d.q d.p
              BB6.Agent2PacketOneReentry.fixedTail))
          (BB6.Agent2BoundaryBZero.regularSection a 1 5) := by
      simpa [a,ha',hq,BB6.Agent2PacketOneReentry.fixedTail] using
        (show ObsEq
          (run (12*k*k+49*k+40)
            (packet (3*k+2) 0 d.p (false::List.replicate 6 true)))
          (BB6.Agent2BoundaryBZero.regularSection (8*k+9+d.p) 1 5) by
          rw [h]
          exact BB6.Padding.cfgEq_refl _)
    simpa only [regularSection_sourceSection a 1 5 hfloor] using hreg
  · obtain ⟨hE,hpSmall⟩ := hE
    have hp0 : d.p=0 := by
      rcases hpSmall with hzero | hone
      · exact hzero
      · omega
    let k : Nat := (d.a-4)/3
    have ha' : d.a=3*k+4 := by dsimp [k]; omega
    let a : Nat := 8*k+5
    have hfloor : 2 ≤ a := by dsimp [a]; omega
    refine ⟨12*k*k+49*k+50+4*d.q,a,1,2*d.q+11,?_,
      canon_nonzero_q a 1 (2*d.q+11) hfloor (by decide)⟩
    have h := BB6.Agent2PacketZeroBoundary.e_zero_boundary k d.q
    have hreg :
        ObsEq
          (run (12*k*k+49*k+50+4*d.q)
            (packet d.a d.q d.p
              BB6.Agent2PacketOneReentry.fixedTail))
          (BB6.Agent2BoundaryBZero.regularSection a 1 (2*d.q+11)) := by
      simpa [a,ha',hp0,BB6.Agent2PacketOneReentry.fixedTail] using
        (show ObsEq
          (run (12*k*k+49*k+50+4*d.q)
            (packet (3*k+4) d.q 0 (false::List.replicate 6 true)))
          (BB6.Agent2BoundaryBZero.regularSection (8*k+5) 1 (2*d.q+11)) by
          rw [h]
          exact BB6.Padding.cfgEq_refl _)
    simpa only [regularSection_sourceSection a 1 (2*d.q+11) hfloor] using hreg

/-- Canonical source-section form of the p=1 mod 3 safe terminal cases. -/
theorem one_terminal_regular_canonical
    (d : BB6.Agent31PacketRank.Packet)
    (ha : d.a ≥ 4) (hp : d.p % 3 = 1)
    (hc : d.a % 3 = 0 ∨
      (d.a % 3 = 2 ∧ d.q = 0) ∨
      (d.a % 3 = 1 ∧ (d.p = 0 ∨ d.p = 1))) :
    ∃ T a q b,
      ObsEq
        (run T (packet d.a d.q d.p
          BB6.Agent2PacketOneReentry.fixedTail))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  rcases hc with hA | hB | hE
  · let k : Nat := (d.a-3)/3
    let r : Nat := (d.p-1)/3
    have ha' : d.a = 3*k+3 := by dsimp [k]; omega
    have hp' : d.p = 3*r+1 := by dsimp [r]; omega
    let a : Nat := BB6.Agent2AOneBoundary.aUnary k d.q r
    have hfloor : 2 ≤ a := by
      dsimp [a,BB6.Agent2AOneBoundary.aUnary]
      omega
    refine ⟨BB6.Agent2AOneBoundary.aCost k d.q r,
      a,0,0,?_,canon_zero_q a hfloor⟩
    have h := BB6.Agent2AOneBoundary.a_p1_boundary k d.q r
    have hreg :
        ObsEq
          (run (BB6.Agent2AOneBoundary.aCost k d.q r)
            (packet d.a d.q d.p
              BB6.Agent2PacketOneReentry.fixedTail))
          (BB6.Agent2BoundaryBZero.regularSection a 0 0) := by
      simpa [a,ha',hp',BB6.Agent2PacketOneReentry.fixedTail,
        BB6.Agent2BoundaryBZero.regularSection,oppairs] using h
    simpa only [regularSection_sourceSection a 0 0 hfloor] using hreg
  · obtain ⟨hB,hq⟩ := hB
    let k : Nat := (d.a-2)/3
    have ha' : d.a = 3*k+2 := by dsimp [k]; omega
    let a : Nat := 8*k+9+d.p
    have hfloor : 2 ≤ a := by dsimp [a]; omega
    refine ⟨12*k*k+49*k+40,a,1,5,?_,
      canon_nonzero_q a 1 5 hfloor (by decide)⟩
    have h := BB6.Agent2BoundaryBZero.b_zero_source k d.p
    have hreg :
        ObsEq
          (run (12*k*k+49*k+40)
            (packet d.a d.q d.p
              BB6.Agent2PacketOneReentry.fixedTail))
          (BB6.Agent2BoundaryBZero.regularSection a 1 5) := by
      simpa [a,ha',hq,BB6.Agent2PacketOneReentry.fixedTail] using
        (show ObsEq
          (run (12*k*k+49*k+40)
            (packet (3*k+2) 0 d.p (false::List.replicate 6 true)))
          (BB6.Agent2BoundaryBZero.regularSection (8*k+9+d.p) 1 5) by
          rw [h]
          exact BB6.Padding.cfgEq_refl _)
    simpa only [regularSection_sourceSection a 1 5 hfloor] using hreg
  · obtain ⟨hE,hpSmall⟩ := hE
    have hp1 : d.p=1 := by
      rcases hpSmall with hzero | hone
      · omega
      · exact hone
    let k : Nat := (d.a-4)/3
    have ha' : d.a=3*k+4 := by dsimp [k]; omega
    have hfloor : 2 ≤ d.a := by omega
    refine ⟨0,d.a,d.q+2,5,?_,
      canon_nonzero_q d.a (d.q+2) 5 hfloor (by omega)⟩
    have hreg :
        ObsEq
          (run 0 (packet d.a d.q d.p
            BB6.Agent2PacketOneReentry.fixedTail))
          (BB6.Agent2BoundaryBZero.regularSection d.a (d.q+2) 5) := by
      change ObsEq
        (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail)
        (BB6.Agent2BoundaryBZero.regularSection d.a (d.q+2) 5)
      rw [ha',hp1]
      rw [BB6.Agent2BoundaryBZero.e_one_regular]
      exact BB6.Padding.cfgEq_refl _
    simpa only [regularSection_sourceSection d.a (d.q+2) 5 hfloor] using hreg

/-- Every safe fixed-tail packet returns to a canonical DRegular source
    section, with the endpoint floor and q/b canonicality exposed. -/
theorem all_safe_packets_canonical
    (c : BB6.Agent31PacketRank.Packet)
    (ha : c.a ≥ 4) (hp : c.p % 3 ≠ 2) :
    ∃ T a q b,
      ObsEq
        (run T (packet c.a c.q c.p
          BB6.Agent2PacketOneReentry.fixedTail))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  let d : BB6.Agent31PacketRank.Packet :=
    (BB6.Agent31PacketRank.normalizeWithCount c).2
  obtain ⟨T,hraw⟩ :=
    BB6.Agent2PacketNormalizeSource.normalized_original_source c ha
      BB6.Agent2PacketOneReentry.fixedTail
  have hraw' :
      run T (packet c.a c.q c.p
        BB6.Agent2PacketOneReentry.fixedTail) =
      packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail := by
    simpa [d,physical,toState,packet,word] using hraw
  have hfirst :
      ObsEq
        (run T (packet c.a c.q c.p
          BB6.Agent2PacketOneReentry.fixedTail))
        (packet d.a d.q d.p
          BB6.Agent2PacketOneReentry.fixedTail) := by
    rw [hraw']
    exact BB6.Padding.cfgEq_refl _
  have hb :
      d.a % 3 = 0 ∨
        (d.a % 3 = 2 ∧ d.q=0) ∨
        (d.a % 3 = 1 ∧ (d.p=0 ∨ d.p=1)) := by
    simpa [d] using
      (BB6.Agent2PacketSafe.normalize_safe_exit c ha (by omega))
  have hamin : d.a ≥ 4 := by
    simpa [d] using BB6.Agent2PacketSafe.normalize_amin c ha
  have hpmodEq : d.p % 3 = c.p % 3 := by
    simpa [d] using BB6.Agent2PacketSafe.normalize_pmod c
  by_cases hzero : c.p % 3 = 0
  · have hp0 : d.p % 3 = 0 := by
      rw [hpmodEq]
      exact hzero
    obtain ⟨S,a,q,b,hboundary,hcanon⟩ :=
      zero_terminal_regular_canonical d hamin hp0 hb
    exact ⟨T+S,a,q,b,
      source_chain T S
        (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail)
        (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail)
        (DRegularSource.sourceSection ⟨a,q,b⟩)
        hfirst hboundary,
      hcanon⟩
  · have hp1 : d.p % 3 = 1 := by
      rw [hpmodEq]
      omega
    obtain ⟨S,a,q,b,hboundary,hcanon⟩ :=
      one_terminal_regular_canonical d hamin hp1 hb
    exact ⟨T+S,a,q,b,
      source_chain T S
        (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail)
        (packet d.a d.q d.p BB6.Agent2PacketOneReentry.fixedTail)
        (DRegularSource.sourceSection ⟨a,q,b⟩)
        hfirst hboundary,
      hcanon⟩

/-- Every E-exit L(3*k+4,q,1) with q>=2 and q not 1 mod 3
    reaches a canonical DRegular source section. The first E return
    gives M(8*k+5,0,2*q;0 1^6); the safe packet normalizer then
    returns to the regular source language. -/
theorem all_E_safe_reentry_canonical
    (k q : Nat) (hq : 2 ≤ q) (hclass : q % 3 ≠ 1) :
    ∃ T a q' b,
      ObsEq
        (run (BB6.Agent32EAll.duration k (q-1) + T)
          (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (DRegularSource.sourceSection ⟨a,q',b⟩) ∧
      DRegular.Canon ⟨a,q',b⟩ := by
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
  have ha : c.a ≥ 4 := by dsimp [c]; omega
  have hp : c.p % 3 ≠ 2 := by dsimp [c]; omega
  obtain ⟨S,a,q',b,hpacket,hcanon⟩ :=
    all_safe_packets_canonical c ha hp
  exact ⟨S,a,q',b,
    source_chain (BB6.Agent32EAll.duration k (q-1)) S
      (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
      (packet c.a c.q c.p
        BB6.Agent2PacketOneReentry.fixedTail)
      (DRegularSource.sourceSection ⟨a,q',b⟩)
      hE hpacket,
    hcanon⟩

#print axioms zero_terminal_regular_canonical
#print axioms one_terminal_regular_canonical
#print axioms all_safe_packets_canonical
#print axioms all_E_safe_reentry_canonical

end BB6.Agent37ExceptionalESafeCanonical
