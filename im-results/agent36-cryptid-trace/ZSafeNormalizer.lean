import Lean.Elab.Tactic.Omega
import EZeroZ
import PacketNormalizeSource
import MarkerZeroAZero

namespace BB6.Agent36ZSafeNormalizer
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerZero BB6.Agent2BoundaryBZero
open BB6.Agent36EZeroZ BB6.BoundaryPadding BB6.Padding

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

/-- Fully source-supported exits after guarded B/E packet normalization:
    p=1 modulo 3, the A/p=0 terminal, or the B/q=0 terminal. -/
def terminalSafe (d : Packet) : Prop :=
  d.p % 3 = 1 ∨
  (d.a % 3 = 0 ∧ d.p % 3 = 0) ∨
  (d.a % 3 = 2 ∧ d.q = 0)

theorem terminalSafe_source (m : Nat) (d : Packet)
    (ha : d.a ≥ 4) (hs : terminalSafe d) :
    ∃ T a q b,
      ObsEq (run T (packet d.a d.q d.p (marker m)))
        (regularSection a q b) := by
  rcases hs with hp | hA | hB
  · exact all_p1_regular m d ha hp
  · obtain ⟨ha0,hp0⟩ := hA
    let ka : Nat := (d.a-3)/3
    let rr : Nat := d.p/3
    have hka : d.a = 3*ka+3 := by dsimp [ka]; omega
    have hrr : d.p = 3*rr := by dsimp [rr]; omega
    rw [hka,hrr]
    exact BB6.Agent2MarkerZeroAZero.aZeroRegular ka d.q rr m
  · obtain ⟨ha2,hq0⟩ := hB
    let kb : Nat := (d.a-2)/3
    have hkb : d.a = 3*kb+2 := by dsimp [kb]; omega
    refine ⟨12*kb*kb+49*kb+40,8*kb+9+d.p,m,0,?_⟩
    rw [hkb,hq0]
    exact b_zero kb d.p m

/-- A recursively decidable-in-principle sufficient condition on every
    packet M(a,q,p;Z_m): normalize the guarded B/E packet phase; either
    reach a source-supported terminal, or reach E/p=0 and consume one
    Z marker level. The remaining cases are deliberately unclassified. -/
def safeZ : Nat → Packet → Prop
  | 0, c =>
      let d := (normalizeWithCount c).2
      terminalSafe d ∨ (d.a % 3 = 1 ∧ d.p = 0)
  | m+1, c =>
      let d := (normalizeWithCount c).2
      terminalSafe d ∨
        (d.a % 3 = 1 ∧ d.p = 0 ∧
          safeZ m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩)

/-- Source soundness for the entire variable-depth safe packet
    normalization procedure. Every certified positive result is a
    finite actual run of the ORIGINAL six-state D machine, up to
    physical equivalence of irrelevant blank padding. -/
theorem safeZ_source (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hs : safeZ m c) :
    ∃ T a q b,
      ObsEq (run T (packet c.a c.q c.p (marker m)))
        (regularSection a q b) := by
  induction m generalizing c with
  | zero =>
    let d : Packet := (normalizeWithCount c).2
    change terminalSafe d ∨ (d.a % 3 = 1 ∧ d.p = 0) at hs
    have hd : d.a ≥ 4 :=
      BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker 0)
    change run Tp (packet c.a c.q c.p (marker 0)) =
      packet d.a d.q d.p (marker 0) at hpath
    rcases hs with hgood | hE
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalSafe_source 0 d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · obtain ⟨hmod,hzero⟩ := hE
      let ke : Nat := (d.a-4)/3
      have hshape : d.a = 3*ke+4 := by
        dsimp [ke]
        omega
      refine ⟨Tp+(12*ke*ke+49*ke+50+4*d.q),8*ke+5,1,2*d.q+5,?_⟩
      rw [run_add,hpath,hshape,hzero]
      exact e_zero_Z0_regular ke d.q
  | succ m ih =>
    let d : Packet := (normalizeWithCount c).2
    change terminalSafe d ∨
      (d.a % 3 = 1 ∧ d.p = 0 ∧
        safeZ m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) at hs
    have hd : d.a ≥ 4 :=
      BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker (m+1))
    change run Tp (packet c.a c.q c.p (marker (m+1))) =
      packet d.a d.q d.p (marker (m+1)) at hpath
    rcases hs with hgood | hE
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalSafe_source (m+1) d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · obtain ⟨hmod,hzero,hrec⟩ := hE
      let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+7⟩
      have hshape : d.a = 3*ke+4 := by
        dsimp [ke]
        omega
      have hnext : safeZ m next := by
        simpa only [next,ke] using hrec
      have hnmin : next.a ≥ 4 := by dsimp [next]; omega
      obtain ⟨Te,a,q,b,hregular⟩ := ih next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+50+4*d.q)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,hzero]
      rw [run_add,e_zero_drop_Z]
      simpa only [next] using hregular

/-- A compressed source-certified criterion for ALL E/p=0 zero-ended
    marker cylinders. The recursion test depends only on k, q, m,
    not on any noncomputable assertion about blank-orbit reachability. -/
theorem e_zero_safeZ (k q m : Nat)
    (hs : safeZ m ⟨8*k+5,0,2*q+7⟩) :
    ∃ T a r b,
      ObsEq (run T (packet (3*k+4) q 0 (marker (m+1))))
        (regularSection a r b) := by
  obtain ⟨Tr,a,r,b,hregular⟩ :=
    safeZ_source m ⟨8*k+5,0,2*q+7⟩
      (by dsimp; omega) hs
  refine ⟨(12*k*k+49*k+50+4*q)+Tr,a,r,b,?_⟩
  rw [run_add,e_zero_drop_Z]
  exact hregular

#print axioms terminalSafe_source
#print axioms safeZ_source
#print axioms e_zero_safeZ
end BB6.Agent36ZSafeNormalizer
