import Lean.Elab.Tactic.Omega
import ZSafeNormalizer
import ZMarkerATwo

namespace BB6.Agent26ZSafePlus
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerZero BB6.Agent2BoundaryBZero
open BB6.Agent36EZeroZ BB6.Agent36ZSafeNormalizer
open BB6.BoundaryPadding BB6.Padding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- The previously missing A/p=2 case is safe at every zero-marker depth,
    not just at marker depth zero. -/
def terminalSafePlus (d : Packet) : Prop :=
  terminalSafe d ∨ (d.a % 3 = 0 ∧ d.p % 3 = 2)

theorem terminalSafePlus_source (m : Nat) (d : Packet)
    (ha : d.a ≥ 4) (hs : terminalSafePlus d) :
    ∃ T a q b,
      ObsEq (run T (packet d.a d.q d.p (marker m)))
        (regularSection a q b) := by
  rcases hs with hOld | hTwo
  · exact terminalSafe_source m d ha hOld
  · obtain ⟨ha0,hp2⟩ := hTwo
    let k := (d.a-3)/3
    let r := (d.p-2)/3
    have hk : d.a = 3*k+3 := by dsimp [k]; omega
    have hr : d.p = 3*r+2 := by dsimp [r]; omega
    refine ⟨BB6.Agent26ZMarkerATwo.twoCost k d.q r m,
      BB6.Agent26ZMarkerATwo.twoUnary k d.q r,
      1,2*m+5,?_⟩
    rw [hk,hr]
    exact BB6.Agent26ZMarkerATwo.a_two_Z_regular k d.q r m

/-- Structural marker-depth recursion and the existing guarded B/E
    rank descent. A/p2 terminals now close without consuming a marker. -/
def safeZPlus : Nat → Packet → Prop
  | 0, c =>
      let d := (normalizeWithCount c).2
      terminalSafePlus d ∨ (d.a % 3 = 1 ∧ d.p = 0)
  | m+1, c =>
      let d := (normalizeWithCount c).2
      terminalSafePlus d ∨
        (d.a % 3 = 1 ∧ d.p = 0 ∧
          safeZPlus m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩)

/-- Original six-state soundness of every accepted expanded zero-marker
    packet, for arbitrary rank, marker depth and source unary prefix. -/
theorem safeZPlus_source (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hs : safeZPlus m c) :
    ∃ T a q b,
      ObsEq (run T (packet c.a c.q c.p (marker m)))
        (regularSection a q b) := by
  induction m generalizing c with
  | zero =>
    let d : Packet := (normalizeWithCount c).2
    change terminalSafePlus d ∨ (d.a % 3 = 1 ∧ d.p = 0) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ := normalized_original_source c ha (marker 0)
    change run Tp (packet c.a c.q c.p (marker 0)) =
      packet d.a d.q d.p (marker 0) at hpath
    rcases hs with hgood | hE
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalSafePlus_source 0 d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · obtain ⟨hmod,hzero⟩ := hE
      let ke : Nat := (d.a-4)/3
      have hshape : d.a = 3*ke+4 := by dsimp [ke]; omega
      refine ⟨Tp+(12*ke*ke+49*ke+50+4*d.q),8*ke+5,1,2*d.q+5,?_⟩
      rw [run_add,hpath,hshape,hzero]
      exact e_zero_Z0_regular ke d.q
  | succ m ih =>
    let d : Packet := (normalizeWithCount c).2
    change terminalSafePlus d ∨
      (d.a % 3 = 1 ∧ d.p = 0 ∧
        safeZPlus m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker (m+1))
    change run Tp (packet c.a c.q c.p (marker (m+1))) =
      packet d.a d.q d.p (marker (m+1)) at hpath
    rcases hs with hgood | hE
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalSafePlus_source (m+1) d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · obtain ⟨hmod,hzero,hrec⟩ := hE
      let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+7⟩
      have hshape : d.a = 3*ke+4 := by dsimp [ke]; omega
      have hnext : safeZPlus m next := by
        simpa only [next,ke] using hrec
      have hnmin : next.a ≥ 4 := by dsimp [next]; omega
      obtain ⟨Te,a,q,b,hregular⟩ := ih next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+50+4*d.q)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,hzero]
      rw [run_add,e_zero_drop_Z]
      simpa only [next] using hregular

/-- All A-index packet terminals with at least four unary symbols are
    source-regularizing at EVERY zero-marker depth and EVERY p residue. -/
theorem all_A_Z_regular (a q p m : Nat) (ha : a ≥ 4)
    (hA : a % 3 = 0) :
    ∃ T A Q B,
      ObsEq (run T (packet a q p (marker m)))
        (regularSection A Q B) := by
  apply terminalSafePlus_source m ⟨a,q,p⟩ ha
  have hp : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hp with hp0 | hp1 | hp2
  · exact Or.inl (Or.inr (Or.inl ⟨hA,hp0⟩))
  · exact Or.inl (Or.inl hp1)
  · exact Or.inr ⟨hA,hp2⟩

/-- Every E/p0 zero marker with k=3t+2 closes for ALL q and all
    positive marker depths. The E drop gives an A-index packet and
    all three A p-residues are source certified. -/
theorem e_zero_k2_all_Z_regular (t q m : Nat) :
    ∃ T A Q B,
      ObsEq
        (run T (packet (9*t+10) q 0 (marker (m+1))))
        (regularSection A Q B) := by
  let k : Nat := 3*t+2
  let a : Nat := 8*k+5
  have ha : a ≥ 4 := by dsimp [a,k]; omega
  have ha0 : a % 3 = 0 := by dsimp [a,k]; omega
  obtain ⟨Te,A,Q,B,hReg⟩ :=
    all_A_Z_regular a 0 (2*q+7) m ha ha0
  refine ⟨(12*k*k+49*k+50+4*q)+Te,A,Q,B,?_⟩
  have hk : 9*t+10 = 3*k+4 := by dsimp [k]; omega
  rw [hk,run_add,e_zero_drop_Z]
  simpa only [a,k] using hReg

/-- Explicit original-machine TWO-section certificate for the formerly
    missing k≡2, q≡2 (mod 3) E/p0 zero-marker branch. The second
    section consumes an A/p2 marker of arbitrary depth. -/
theorem e_zero_k2_q2_exact (t u m : Nat) :
    ObsEq
      (run
        ((12*(3*t+2)*(3*t+2)+49*(3*t+2)+50+4*(3*u+2)) +
          BB6.Agent26ZMarkerATwo.twoCost (8*t+6) 0 (2*u+3) m)
        (packet (9*t+10) (3*u+2) 0 (marker (m+1))))
      (regularSection
        (BB6.Agent26ZMarkerATwo.twoUnary (8*t+6) 0 (2*u+3))
        1 (2*m+5)) := by
  have hindex : 9*t+10 = 3*(3*t+2)+4 := by omega
  have hA : 8*(3*t+2)+5 = 3*(8*t+6)+3 := by omega
  have hp : 2*(3*u+2)+7 = 3*(2*u+3)+2 := by omega
  rw [hindex,run_add,e_zero_drop_Z,hA,hp]
  exact BB6.Agent26ZMarkerATwo.a_two_Z_regular
    (8*t+6) 0 (2*u+3) m

/-- The new predicate accepts every packet accepted by the original. -/
theorem old_safe_included (m : Nat) (c : Packet)
    (h : safeZ m c) : safeZPlus m c := by
  induction m generalizing c with
  | zero =>
    change terminalSafe ((normalizeWithCount c).2) ∨
      (((normalizeWithCount c).2).a % 3 = 1 ∧
       ((normalizeWithCount c).2).p = 0) at h
    change terminalSafePlus ((normalizeWithCount c).2) ∨
      (((normalizeWithCount c).2).a % 3 = 1 ∧
       ((normalizeWithCount c).2).p = 0)
    rcases h with hgood | hE
    · exact Or.inl (Or.inl hgood)
    · exact Or.inr hE
  | succ m ih =>
    let d := (normalizeWithCount c).2
    change terminalSafe d ∨
      (d.a%3=1 ∧ d.p=0 ∧
        safeZ m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) at h
    change terminalSafePlus d ∨
      (d.a%3=1 ∧ d.p=0 ∧
        safeZPlus m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩)
    rcases h with hgood | ⟨ha,hp,hr⟩
    · exact Or.inl (Or.inl hgood)
    · exact Or.inr ⟨ha,hp,ih _ hr⟩

/-- This concrete packet was excluded by the earlier sufficient predicate. -/
theorem newly_accepted : safeZPlus 1 ⟨6,0,2⟩ := by
  simp [safeZPlus, terminalSafePlus, terminalSafe, normalizeWithCount, advance]
theorem genuinely_new : ¬ safeZ 1 ⟨6,0,2⟩ := by
  simp [safeZ, terminalSafe, normalizeWithCount, advance]

/-- Previously rejected finite-depth test from Agent36's dossier. -/
theorem residual_52_accepted : safeZPlus 3 ⟨52,1,0⟩ := by
  simp [safeZPlus, terminalSafePlus, terminalSafe, normalizeWithCount, advance]

#print axioms terminalSafePlus_source
#print axioms safeZPlus_source
#print axioms e_zero_k2_q2_exact
#print axioms all_A_Z_regular
#print axioms e_zero_k2_all_Z_regular
#print axioms old_safe_included
#print axioms residual_52_accepted
end BB6.Agent26ZSafePlus
