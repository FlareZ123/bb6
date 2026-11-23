import Lean.Elab.Tactic.Omega
import AY1P2Regular
import ZSafePlus
import EAltPacketCompose

/-!
  Mixed Y-marker and Z-marker source-connected reduction:
  1. original guarded B/E rank normalizer;
  2. positive-depth A/p=0 and p=2 (at depths 1,2,3) source exits;
  3. E/p0 positive-depth Y->Y marker decrement;
  4. E/p2 positive-depth Y->Z, then source-sound ZSafePlus;
  5. at depth zero E/p=0 or p=2 packet is already regular.

  All source transitions are on the literal original Cryptid D machine,
  with CfgEq physical-padding equivalence. No blank-root reachability.
-/
namespace BB6.Agent36YPlus

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent31PacketRank BB6.Agent2PacketNormalizeSource
open BB6.Agent2MarkerTower (marker)
open BB6.Agent2BoundaryBZero
open BB6.BoundaryPadding

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

private theorem oppairs_snoc (q : Nat) :
    oppairs q ++ [false,true] = oppairs (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,List.append_assoc] using
      congrArg (fun xs : List Bool => [false,true] ++ xs) ih

def terminalYPlus (m : Nat) (d : Packet) : Prop :=
  BB6.Agent36YSafe.terminalYSafe m d ∨
  ((m=1 ∨ m=2 ∨ m=3) ∧ d.a%3=0 ∧ d.p%3=2)

theorem terminalYPlus_source (m : Nat) (d : Packet)
    (ha : d.a ≥ 4) (hs : terminalYPlus m d) :
    ∃ T a q b,
      ObsEq (run T (packet d.a d.q d.p (marker m)))
        (regularSection a q b) := by
  rcases hs with hbase | ⟨hm,ha0,hp2⟩
  · exact BB6.Agent36YSafe.terminalYSafe_source m d ha hbase
  let ka : Nat := (d.a-3)/3
  let rr : Nat := (d.p-2)/3
  have hka : d.a=3*ka+3 := by dsimp [ka]; omega
  have hrr : d.p=3*rr+2 := by dsimp [rr]; omega
  rcases hm with hm1 | hm2 | hm3
  · rw [hm1,hka,hrr]
    exact BB6.Agent36AY1.regular ka d.q rr
  · rw [hm2,hka,hrr]
    exact BB6.Agent36AY2.a_two_y2_regular ka d.q rr
  · rw [hm3,hka]
    exact BB6.Agent35MarkerOne.a_marker_regular ka d.q d.p

/-- Empty-depth marker Y0=11 turns E/p2 immediately into canonical L. -/
theorem e_two_y0 (a q : Nat) :
    packet a q 2 (marker 0) = regularSection a (q+1) 3 := by
  have h := oppairs_snoc q
  simp only [packet,word,marker,regularSection,List.nil_append]
  rw [←h]
  simp [oppairs,List.append_assoc]

/-- Mixed Y/Z depth-recursive source closure. The non-A residual classes
    are deliberately not claimed unsafe or nonhalting. -/
def safeYPlus : Nat → Packet → Prop
  | 0,c =>
      let d := (normalizeWithCount c).2
      terminalYPlus 0 d ∨ (d.a%3=1 ∧ (d.p=0 ∨ d.p=2))
  | m+1,c =>
      let d := (normalizeWithCount c).2
      terminalYPlus (m+1) d ∨
        (d.a%3=1 ∧ d.p=0 ∧
          safeYPlus m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) ∨
        (d.a%3=1 ∧ d.p=2 ∧
          BB6.Agent26ZSafePlus.safeZPlus (m+2)
            ⟨8*((d.a-4)/3)+5,0,2*d.q+6⟩)

theorem safeYPlus_source (m : Nat) (c : Packet) (ha : c.a ≥ 4)
    (hs : safeYPlus m c) :
    ∃ T a q b,
      ObsEq (run T (packet c.a c.q c.p (marker m)))
        (regularSection a q b) := by
  induction m generalizing c with
  | zero =>
    let d : Packet := (normalizeWithCount c).2
    change terminalYPlus 0 d ∨
      (d.a%3=1 ∧ (d.p=0 ∨ d.p=2)) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker 0)
    change run Tp (packet c.a c.q c.p (marker 0)) =
      packet d.a d.q d.p (marker 0) at hpath
    rcases hs with hgood | ⟨hE,hp0 | hp2⟩
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalYPlus_source 0 d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · refine ⟨Tp,d.a,d.q+1,1,?_⟩
      rw [hpath,hp0,BB6.Agent36YSafe.e_zero_y0]
      exact BB6.Padding.cfgEq_refl _
    · refine ⟨Tp,d.a,d.q+1,3,?_⟩
      rw [hpath,hp2,e_two_y0]
      exact BB6.Padding.cfgEq_refl _
  | succ m ih =>
    let d : Packet := (normalizeWithCount c).2
    change terminalYPlus (m+1) d ∨
      (d.a%3=1 ∧ d.p=0 ∧
        safeYPlus m ⟨8*((d.a-4)/3)+5,0,2*d.q+7⟩) ∨
      (d.a%3=1 ∧ d.p=2 ∧
        BB6.Agent26ZSafePlus.safeZPlus (m+2)
          ⟨8*((d.a-4)/3)+5,0,2*d.q+6⟩) at hs
    have hd : d.a ≥ 4 := BB6.Agent2PacketSafe.normalize_amin c ha
    obtain ⟨Tp,hpath⟩ :=
      normalized_original_source c ha (marker (m+1))
    change run Tp (packet c.a c.q c.p (marker (m+1))) =
      packet d.a d.q d.p (marker (m+1)) at hpath
    rcases hs with hgood | ⟨hE,hzero,hrec⟩ | ⟨hE,htwo,hZ⟩
    · obtain ⟨Te,a,q,b,hregular⟩ :=
        terminalYPlus_source (m+1) d hd hgood
      refine ⟨Tp+Te,a,q,b,?_⟩
      rw [run_add,hpath]
      exact hregular
    · let ke : Nat := (d.a-4)/3
      let next : Packet := ⟨8*ke+5,0,2*d.q+7⟩
      have hshape : d.a=3*ke+4 := by dsimp [ke]; omega
      have hnext : safeYPlus m next := by
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
      have hnext : BB6.Agent26ZSafePlus.safeZPlus (m+2) next := by
        simpa only [next,ke] using hZ
      have hnmin : next.a ≥ 4 := by change 8*ke+5≥4; omega
      obtain ⟨Te,a,q,b,hregular⟩ :=
        BB6.Agent26ZSafePlus.safeZPlus_source
          (m+2) next hnmin hnext
      refine ⟨Tp+((12*ke*ke+49*ke+68+4*d.q+6*m)+Te),a,q,b,?_⟩
      rw [run_add,hpath,hshape,htwo]
      rw [run_add,BB6.Agent2EAltPacketCompose.e_two_to_zero]
      simpa only [next] using hregular

/-- E/p2 fixed suffix Y3 reset to the combined source Y/Z grammar. -/
theorem p2_fixed_safeYPlus (k Q : Nat)
    (hs : safeYPlus 3 ⟨8*k+5,0,2*Q+6⟩) :
    ∃ T a q b,
      ObsEq
        (run T (packet (3*k+4) Q 2
          (false::List.replicate 6 true)))
        (regularSection a q b) := by
  obtain ⟨Te,a,q,b,hreg⟩ :=
    safeYPlus_source 3 ⟨8*k+5,0,2*Q+6⟩
      (by change 8*k+5≥4; omega) hs
  refine ⟨BB6.Agent2PacketP2Reset.eTwoTime k Q+Te,a,q,b,?_⟩
  rw [run_add,BB6.Agent2PacketP2Reset.e_two_reset]
  exact hreg

#print axioms terminalYPlus_source
#print axioms e_two_y0
#print axioms safeYPlus_source
#print axioms p2_fixed_safeYPlus
end BB6.Agent36YPlus
