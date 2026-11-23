import Lean.Elab.Tactic.Omega
import YPlusZClosure
import ZSafeK0

/-!
  Enlarged cross-marker source classifier: preserve every previously
  YPlus-accepted prepared packet, and allow a Y/p2 exceptional turn to
  enter the now source-certified ZSafeK0 terminal grammar (E/p2,Z_m,
  positive q, underlying E index k divisible by 3).

  This is a compositional all-depth original six-state soundness result;
  not a characterization of the genuine blank-root orbit.
-/
namespace BB6.Agent36YPlusK0

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerTower (marker)
open BB6.Agent2BoundaryBZero BB6.BoundaryPadding

set_option maxHeartbeats 18000000
set_option maxRecDepth 8192

def safeYPlusK0 : Nat → Packet → Prop
  | 0,c => BB6.Agent36YPlus.safeYPlus 0 c
  | m+1,c =>
      BB6.Agent36YPlus.safeYPlus (m+1) c ∨
      let d := (normalizeWithCount c).2
      (d.a%3=1 ∧ d.p=0 ∧
        safeYPlusK0 m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) ∨
      (d.a%3=1 ∧ d.p=2 ∧
        BB6.Agent36ZK0.safeZK0 (m+2)
          ⟨8*((d.a-4)/3)+5,0,2*d.q+6⟩)

/-- This new original-machine return predicate is conservative over
    the entire existing physically verified mixed Y/Z language. -/
theorem old_included (m : Nat) (c : Packet)
    (hs : BB6.Agent36YPlus.safeYPlus m c) :
    safeYPlusK0 m c := by
  cases m with
  | zero => exact hs
  | succ m => exact Or.inl hs

/-- Source-soundness of each newly accepted nested Y/Z marker packet. -/
theorem safeYPlusK0_source (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hs : safeYPlusK0 m c) :
    ∃ T a q b,
      ObsEq (run T (packet c.a c.q c.p (marker m)))
        (regularSection a q b) := by
  induction m generalizing c with
  | zero =>
    exact BB6.Agent36YPlus.safeYPlus_source 0 c ha hs
  | succ m ih =>
    change BB6.Agent36YPlus.safeYPlus (m+1) c ∨
      (let d := (normalizeWithCount c).2
       (d.a%3=1 ∧ d.p=0 ∧
         safeYPlusK0 m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) ∨
       (d.a%3=1 ∧ d.p=2 ∧
         BB6.Agent36ZK0.safeZK0 (m+2)
           ⟨8*((d.a-4)/3)+5,0,2*d.q+6⟩)) at hs
    rcases hs with hold | hnew
    · exact BB6.Agent36YPlus.safeYPlus_source (m+1) c ha hold
    let d : Packet := (normalizeWithCount c).2
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    change
      (d.a%3=1 ∧ d.p=0 ∧
        safeYPlusK0 m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) ∨
      (d.a%3=1 ∧ d.p=2 ∧
        BB6.Agent36ZK0.safeZK0 (m+2)
          ⟨8*((d.a-4)/3)+5,0,2*d.q+6⟩) at hnew
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker (m+1))
    change run Tp (packet c.a c.q c.p (marker (m+1))) =
      packet d.a d.q d.p (marker (m+1)) at hpath
    rcases hnew with ⟨hE,hzero,hrec⟩ | ⟨hE,htwo,hZ⟩
    · let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+7⟩
      have hshape : d.a=3*ke+4 := by dsimp [ke]; omega
      have hnext : safeYPlusK0 m next := by
        simpa only [next,ke] using hrec
      have hnmin : next.a ≥ 4 := by change 8*ke+5≥4; omega
      obtain ⟨Te,a,q,b,hregular⟩ := ih next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+50+4*d.q)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,hzero]
      rw [run_add,BB6.Agent2MarkerTower.e_zero_drop]
      simpa only [next] using hregular
    · let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+6⟩
      have hshape : d.a=3*ke+4 := by dsimp [ke]; omega
      have hnext : BB6.Agent36ZK0.safeZK0 (m+2) next := by
        simpa only [next,ke] using hZ
      have hnmin : next.a ≥ 4 := by change 8*ke+5≥4; omega
      obtain ⟨Te,a,q,b,hregular⟩ :=
        BB6.Agent36ZK0.safeZK0_source (m+2) next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+68+4*d.q+6*m)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,htwo]
      rw [run_add,BB6.Agent2EAltPacketCompose.e_two_to_zero]
      simpa only [next] using hregular

/-- Direct fixed original E/p2 suffix-to-regular bridge for all packets
    meeting the expanded Y/Z recursive source criterion. -/
theorem p2_fixed_safeYPlusK0 (k Q : Nat)
    (hs : safeYPlusK0 3 ⟨8*k+5,0,2*Q+6⟩) :
    ∃ T a q b,
      ObsEq
        (run T
          (packet (3*k+4) Q 2
            (false::List.replicate 6 true)))
        (regularSection a q b) := by
  obtain ⟨Te,a,q,b,hreg⟩ :=
    safeYPlusK0_source 3 ⟨8*k+5,0,2*Q+6⟩
      (by change 8*k+5≥4; omega) hs
  refine ⟨BB6.Agent2PacketP2Reset.eTwoTime k Q+Te,a,q,b,?_⟩
  rw [run_add,BB6.Agent2PacketP2Reset.e_two_reset]
  exact hreg

#print axioms old_included
#print axioms safeYPlusK0_source
#print axioms p2_fixed_safeYPlusK0
end BB6.Agent36YPlusK0
