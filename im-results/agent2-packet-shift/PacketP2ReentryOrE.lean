import Lean.Elab.Tactic.Omega
import PacketNormalizeSource
import BoundaryBZero
import AP2PacketBoundarySource
import PacketP2ResetSource

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2PacketP2ReentryOrE

open CryptidBoundary
open BB6.Agent31PacketRank
open BB6.Agent31PacketSource
open BB6.Agent31PacketPaths
open BB6.Agent2PacketNormalizeSource
open BB6.Agent2PacketSafe
open BB6.Agent2AP2PacketBoundary
open BB6.Agent2BoundaryBZero

def fixedTail : List Bool := false :: List.replicate 6 true

/-- Every source-valid p≡2 packet either re-enters regular L after its
    guarded normalization, or reaches the single residual E,p=2 packet
    boundary. The A and B exits are both source-composed here. -/
theorem p2_packet_reentry_or_E (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 = 2) :
    (∃ T a q b,
      run T (packet c.a c.q c.p fixedTail) =
        regularSection a q b) ∨
    (∃ T d,
      run T (packet c.a c.q c.p fixedTail) =
        packet d.a d.q d.p fixedTail ∧
      d.a % 3 = 1 ∧ d.p = 2) := by
  let d : Packet := (normalizeWithCount c).2
  obtain ⟨T0,h0raw⟩ := normalized_original_source c ha fixedTail
  have h0 : run T0 (packet c.a c.q c.p fixedTail) =
      packet d.a d.q d.p fixedTail := by
    simpa [physical,toState,d] using h0raw
  have hexit := normalize_p2_exit c ha hp
  change d.a % 3 = 0 ∨ (d.a % 3 = 2 ∧ d.q = 0) ∨
    (d.a % 3 = 1 ∧ d.p = 2) at hexit
  have hpD : d.p % 3 = 2 := by
    simpa [d,hp] using normalize_pmod c
  have hamin : d.a ≥ 4 := by
    simpa [d] using normalize_amin c ha
  rcases hexit with hA | hRest
  · let k : Nat := (d.a-3)/3
    let r : Nat := (d.p-2)/3
    have hk : 3*k+3=d.a := by dsimp [k]; omega
    have hr : 3*r+2=d.p := by dsimp [r]; omega
    have hshape : packet d.a d.q d.p fixedTail =
        BB6.Agent2AP2PacketBoundary.input k d.q r := by
      simp [BB6.Agent2AP2PacketBoundary.input,
        BB6.Agent2AP2PacketBoundary.fixedTail,
        packet,word,fixedTail,hk,hr]
    have hAP2 :=
      BB6.Agent2AP2PacketBoundary.a_p2_packet_reentry k d.q r
    let a : Nat :=
      2*(4*k+3+CryptidA.wordInc
        (BB6.Agent2AP2PacketBoundary.words d.q r))+5
    have hendpoint :
        BB6.Agent2AP2PacketBoundary.endpoint k d.q r =
          regularSection a 3 3 := by
      simp [a,BB6.Agent2AP2PacketBoundary.endpoint,
        BB6.Agent2BoundaryBZero.regularSection]
    have hfinal :
        run (T0+BB6.Agent2AP2PacketBoundary.sourceTime k d.q r)
          (packet c.a c.q c.p fixedTail) =
          regularSection a 3 3 := by
      rw [run_add,h0,hshape,hAP2,hendpoint]
    exact Or.inl ⟨T0+BB6.Agent2AP2PacketBoundary.sourceTime k d.q r,
      a,3,3,hfinal⟩
  · rcases hRest with hB | hE
    · let k : Nat := (d.a-2)/3
      have hk : 3*k+2=d.a := by dsimp [k]; omega
      have hshape : packet d.a d.q d.p fixedTail =
          packet (3*k+2) 0 d.p fixedTail := by
        simp [packet,word,hk,hB.2]
      have hB0 := BB6.Agent2BoundaryBZero.b_zero_source k d.p
      have hfinal :
          run (T0+(12*k*k+49*k+40))
            (packet c.a c.q c.p fixedTail) =
            regularSection (8*k+9+d.p) 1 5 := by
        rw [run_add,h0,hshape,hB0]
      exact Or.inl ⟨T0+(12*k*k+49*k+40),
        8*k+9+d.p,1,5,hfinal⟩
    · exact Or.inr ⟨T0,d,h0,hE.1,hE.2⟩

/-- Strengthening p2_packet_reentry_or_E: the only residual E,p=2
    branch is immediately converted to the canonical changed-marker reset
    packet used by the arbitrary-depth E-chain analysis. -/
theorem p2_packet_reentry_or_reset (c : Packet) (ha : c.a ≥ 4)
    (hp : c.p % 3 = 2) :
    (∃ T a q b,
      run T (packet c.a c.q c.p fixedTail) =
        regularSection a q b) ∨
    (∃ T k q,
      run T (packet c.a c.q c.p fixedTail) =
        packet (8*k+5) 0 (2*q+6)
          BB6.Agent2PacketP2Reset.marker) := by
  rcases p2_packet_reentry_or_E c ha hp with hL | hE
  · exact Or.inl hL
  · rcases hE with ⟨T0,d,h0,haE,hpE⟩
    have hamin : d.a ≥ 4 := by
      simpa [normalizeWithCount] using normalize_amin c ha
    let k : Nat := (d.a-4)/3
    have hk : 3*k+4=d.a := by dsimp [k]; omega
    have hshape : packet d.a d.q d.p fixedTail =
        packet (3*k+4) d.q 2 fixedTail := by
      simp [hk,hpE]
    have hreset := BB6.Agent2PacketP2Reset.e_two_reset k d.q
    have hfinal :
        run (T0+BB6.Agent2PacketP2Reset.eTwoTime k d.q)
          (packet c.a c.q c.p fixedTail) =
          packet (8*k+5) 0 (2*d.q+6)
            BB6.Agent2PacketP2Reset.marker := by
      rw [run_add,h0,hshape,hreset]
    exact Or.inr ⟨T0+BB6.Agent2PacketP2Reset.eTwoTime k d.q,
      k,d.q,hfinal⟩

#print axioms p2_packet_reentry_or_E
#print axioms p2_packet_reentry_or_reset

end BB6.Agent2PacketP2ReentryOrE
