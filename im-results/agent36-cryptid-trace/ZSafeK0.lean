import Lean.Elab.Tactic.Omega
import EZTwoK0BRegular
import ZSafePlus

/-!
  Extended original-machine Z_m source normalization: recognize the
  previously missing positive-q E/p=2 terminal when its E-index has
  k divisible by three. Its next source turn reaches a B/q0 section
  and then the physical F0 regular language L.

  This is a uniform all-depth recursive decision-sufficient predicate.
  The residue is a *terminal extension*, not a new abstract B/E step.
-/
namespace BB6.Agent36ZK0

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerZero (marker)
open BB6.Agent2BoundaryBZero BB6.BoundaryPadding

set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def terminalZK0 (d : Packet) : Prop :=
  BB6.Agent26ZSafePlus.terminalSafePlus d ∨
    (d.a%3=1 ∧ d.p=2 ∧ d.q>0 ∧ ((d.a-4)/3)%3=0)

theorem terminalZK0_source (m : Nat) (d : Packet)
    (ha : d.a ≥ 4) (hs : terminalZK0 d) :
    ∃ T a q b,
      ObsEq
        (run T (packet d.a d.q d.p (marker m)))
        (regularSection a q b) := by
  rcases hs with hpre | ⟨hE,hp2,hq,hk0⟩
  · exact BB6.Agent26ZSafePlus.terminalSafePlus_source m d ha hpre
  let k : Nat := (d.a-4)/3
  let t : Nat := k/3
  let u : Nat := d.q-1
  have hka : d.a=3*k+4 := by dsimp [k]; omega
  have hkt : k=3*t := by dsimp [t]; omega
  have hq : d.q=u+1 := by dsimp [u]; omega
  rw [hka,hkt,hp2,hq]
  exact BB6.Agent36EZTwoBZero.e_two_Z_k0_regular t u m

def safeZK0 : Nat → Packet → Prop
  | 0,c =>
      let d := (normalizeWithCount c).2
      terminalZK0 d ∨ (d.a%3=1 ∧ d.p=0)
  | m+1,c =>
      let d := (normalizeWithCount c).2
      terminalZK0 d ∨
        (d.a%3=1 ∧ d.p=0 ∧
          safeZK0 m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩)

theorem safeZK0_source (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hs : safeZK0 m c) :
    ∃ T a q b,
      ObsEq (run T (packet c.a c.q c.p (marker m)))
        (regularSection a q b) := by
  induction m generalizing c with
  | zero =>
    let d : Packet := (normalizeWithCount c).2
    change terminalZK0 d ∨ (d.a%3=1 ∧ d.p=0) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker 0)
    change run Tp (packet c.a c.q c.p (marker 0)) =
      packet d.a d.q d.p (marker 0) at hpath
    rcases hs with hgood | ⟨hE,hzero⟩
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalZK0_source 0 d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · let ke : Nat := (d.a-4)/3
      have hshape : d.a=3*ke+4 := by dsimp [ke]; omega
      refine ⟨Tp+(12*ke*ke+49*ke+50+4*d.q),8*ke+5,1,2*d.q+5,?_⟩
      rw [run_add,hpath,hshape,hzero]
      exact BB6.Agent36EZeroZ.e_zero_Z0_regular ke d.q
  | succ m ih =>
    let d : Packet := (normalizeWithCount c).2
    change terminalZK0 d ∨
      (d.a%3=1 ∧ d.p=0 ∧
        safeZK0 m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker (m+1))
    change run Tp (packet c.a c.q c.p (marker (m+1))) =
      packet d.a d.q d.p (marker (m+1)) at hpath
    rcases hs with hgood | ⟨hE,hzero,hrec⟩
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalZK0_source (m+1) d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+7⟩
      have hshape : d.a=3*ke+4 := by dsimp [ke]; omega
      have hnext : safeZK0 m next := by
        simpa only [next,ke] using hrec
      have hnmin : next.a ≥ 4 := by change 8*ke+5≥4; omega
      obtain ⟨Te,a,q,b,hregular⟩ := ih next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+50+4*d.q)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,hzero]
      rw [run_add,BB6.Agent36EZeroZ.e_zero_drop_Z]
      simpa only [next] using hregular

/-- Conservativity: the new source classifier never loses any packet
    already accepted by the previous all-depth ZSafePlus theorem. -/
theorem safeZPlus_included (m : Nat) (c : Packet)
    (hs : BB6.Agent26ZSafePlus.safeZPlus m c) :
    safeZK0 m c := by
  induction m generalizing c with
  | zero =>
    change BB6.Agent26ZSafePlus.terminalSafePlus
      ((normalizeWithCount c).2) ∨
      (((normalizeWithCount c).2).a%3=1 ∧
       ((normalizeWithCount c).2).p=0) at hs
    change terminalZK0 ((normalizeWithCount c).2) ∨
      (((normalizeWithCount c).2).a%3=1 ∧
       ((normalizeWithCount c).2).p=0)
    rcases hs with hg | he
    · exact Or.inl (Or.inl hg)
    · exact Or.inr he
  | succ m ih =>
    let d : Packet := (normalizeWithCount c).2
    change BB6.Agent26ZSafePlus.terminalSafePlus d ∨
      (d.a%3=1 ∧ d.p=0 ∧
        BB6.Agent26ZSafePlus.safeZPlus m
          ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) at hs
    change terminalZK0 d ∨
      (d.a%3=1 ∧ d.p=0 ∧
        safeZK0 m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩)
    rcases hs with hg | ⟨ha,hp,hrec⟩
    · exact Or.inl (Or.inl hg)
    · exact Or.inr ⟨ha,hp,ih _ hrec⟩

#print axioms terminalZK0_source
#print axioms safeZK0_source
#print axioms safeZPlus_included
end BB6.Agent36ZK0
