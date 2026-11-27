import Lean.Elab.Tactic.Omega
import ExceptionalESafeCanonical
import ExceptionalEReentryClassification
import PacketP2ReentryOrE

set_option maxRecDepth 8192
set_option maxHeartbeats 22000000

namespace BB6.Agent37EUniversalDichotomy

open CryptidBoundary BB6.BoundaryPadding BB6.Padding
open BB6.Agent31PacketSource

private theorem regular_eq_source (a q b : Nat) (ha : 2 ≤ a) :
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

/-- One exact original source E prefix for all q>=2, including q≡1
    where the safe regularizer is unavailable. -/
private theorem first_E_packet (k q : Nat) (hq : 2 ≤ q) :
    ObsEq
      (run (BB6.Agent32EAll.duration k (q-1))
        (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
      (packet (8*k+5) 0 (2*q)
        BB6.Agent2PacketOneReentry.fixedTail) := by
  have hq1 : 1 ≤ q := by omega
  have hE := BB6.EExceptionalShift.e_source k (q-1)
  have hE' : ObsEq
      (run (BB6.Agent32EAll.duration k (q-1))
        (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
      (BB6.Agent32EAll.output k (q-1) []) := by
    simpa only [Nat.sub_add_cancel hq1] using hE
  rw [e_output_packet k q hq] at hE'
  exact hE'

/-- Every exceptional E input with at least one alternating pair has
    a finite original-machine path to *either* a DRegular physical section
    *or* a single canonical marked E2 packet family. There is NO
    restriction on k or q, and the two cases are exact and exhaustive.

    Unlike a nonhalting theorem, the second branch is an unresolved
    changed-marker section; this theorem isolates the remaining proof
    obligation instead of assuming that the marker exits. -/
theorem every_E_regular_or_marked_reset (k q : Nat) (hq : 1 ≤ q) :
    (∃ T a q' b,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (BB6.Agent2BoundaryBZero.regularSection a q' b)) ∨
    (∃ T k' Q,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
        (packet (8*k'+5) 0 (2*Q+6)
          BB6.Agent2PacketP2Reset.marker)) := by
  by_cases hq1 : q=1
  · obtain ⟨T,a,q',b,hobs,hcanon⟩ :=
      BB6.Agent37ExceptionalEReentryClassification.all_E_reentry_canonical_except_q1_mod3
        k q (Or.inl hq1)
    have hs := regular_eq_source a q' b hcanon.1
    exact Or.inl ⟨T,a,q',b,by rw [hs]; exact hobs⟩
  · have hq2 : 2 ≤ q := by omega
    by_cases hclass : q % 3 ≠ 1
    · obtain ⟨S,a,q',b,hobs,hcanon⟩ :=
        BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
          k q hq2 hclass
      have hs := regular_eq_source a q' b hcanon.1
      exact Or.inl ⟨BB6.Agent32EAll.duration k (q-1)+S,
        a,q',b,by rw [hs]; exact hobs⟩
    · let c : BB6.Agent31PacketRank.Packet := ⟨8*k+5,0,2*q⟩
      have ha : c.a ≥ 4 := by dsimp [c]; omega
      have hp : c.p % 3 = 2 := by dsimp [c]; omega
      have hfirst : ObsEq
          (run (BB6.Agent32EAll.duration k (q-1))
            (DRegularSource.sourceSection ⟨3*k+4,q,1⟩))
          (packet c.a c.q c.p
            BB6.Agent2PacketOneReentry.fixedTail) := by
        simpa [c] using first_E_packet k q hq2
      rcases BB6.Agent2PacketP2ReentryOrE.p2_packet_reentry_or_reset
          c ha hp with hregular | hreset
      · rcases hregular with ⟨S,a,q',b,hEq⟩
        have hEq' : run S
            (packet c.a c.q c.p
              BB6.Agent2PacketOneReentry.fixedTail) =
            BB6.Agent2BoundaryBZero.regularSection a q' b := by
          simpa [BB6.Agent2PacketOneReentry.fixedTail,
            BB6.Agent2PacketP2ReentryOrE.fixedTail] using hEq
        have hSecond : ObsEq
            (run S (packet c.a c.q c.p
              BB6.Agent2PacketOneReentry.fixedTail))
            (BB6.Agent2BoundaryBZero.regularSection a q' b) := by
          rw [hEq']
          exact BB6.Padding.cfgEq_refl _
        exact Or.inl ⟨BB6.Agent32EAll.duration k (q-1)+S,
          a,q',b,
          source_chain (BB6.Agent32EAll.duration k (q-1)) S
            (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
            (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail)
            (BB6.Agent2BoundaryBZero.regularSection a q' b)
            hfirst hSecond⟩
      · rcases hreset with ⟨S,k',Q,hEq⟩
        have hEq' : run S
            (packet c.a c.q c.p
              BB6.Agent2PacketOneReentry.fixedTail) =
            packet (8*k'+5) 0 (2*Q+6)
              BB6.Agent2PacketP2Reset.marker := by
          simpa [BB6.Agent2PacketOneReentry.fixedTail,
            BB6.Agent2PacketP2ReentryOrE.fixedTail] using hEq
        have hSecond : ObsEq
            (run S (packet c.a c.q c.p
              BB6.Agent2PacketOneReentry.fixedTail))
            (packet (8*k'+5) 0 (2*Q+6)
              BB6.Agent2PacketP2Reset.marker) := by
          rw [hEq']
          exact BB6.Padding.cfgEq_refl _
        exact Or.inr ⟨BB6.Agent32EAll.duration k (q-1)+S,k',Q,
          source_chain (BB6.Agent32EAll.duration k (q-1)) S
            (DRegularSource.sourceSection ⟨3*k+4,q,1⟩)
            (packet c.a c.q c.p BB6.Agent2PacketOneReentry.fixedTail)
            (packet (8*k'+5) 0 (2*Q+6)
              BB6.Agent2PacketP2Reset.marker)
            hfirst hSecond⟩

#print axioms every_E_regular_or_marked_reset

end BB6.Agent37EUniversalDichotomy
