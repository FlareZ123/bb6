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
theorem newly_accepted : safeZPlus 1 ⟨6,0,2⟩ := by decide
theorem genuinely_new : ¬ safeZ 1 ⟨6,0,2⟩ := by decide

/-- Previously rejected finite-depth test from Agent36's dossier. -/
theorem residual_52_accepted : safeZPlus 3 ⟨52,1,0⟩ := by decide

#print axioms terminalSafePlus_source
#print axioms safeZPlus_source
#print axioms old_safe_included
#print axioms residual_52_accepted
end BB6.Agent26ZSafePlus
