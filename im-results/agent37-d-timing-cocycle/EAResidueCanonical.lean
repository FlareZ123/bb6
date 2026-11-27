import Lean.Elab.Tactic.Omega
import EFirstAPacket
import AP2PacketBoundarySource
import PacketRank
import BoundaryBZero

set_option maxRecDepth 8192
set_option maxHeartbeats 18000000

namespace BB6.Agent37EAResidueCanonical

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
      rw [show Nat.succ m+n=(m+n)+1 by omega]
      rw [List.replicate_succ]
      rw [ih]
      rw [←List.cons_append]
      rw [←List.replicate_succ]
  have hrep : List.replicate a true =
      [true,true] ++ List.replicate (a-2) true := by
    rw [show a=2+(a-2) by omega, hrepAdd]
    simp
  rw [hrep]
  simp [List.append_assoc]

/-- The entire E/A exceptional cylinder with E pair-count
    q≡1 mod3 and q>=4 exits through the A/p2 packet boundary
    to an explicitly CANONICAL (q=3,b=2) DRegular section.
    No existential endpoint may hide a noncanonical q=0,b>0 state. -/
theorem ea_q1_residue_canonical (t q : Nat)
    (hq : 2 ≤ q) (hmod : q % 3 = 1) :
    ∃ T a,
      ObsEq
        (run T (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
        (DRegularSource.sourceSection ⟨a,3,2⟩) ∧
      DRegular.Canon ⟨a,3,2⟩ := by
  let r : Nat := (2*q-2)/3
  let ka : Nat := 8*t+6
  let c : BB6.Agent31PacketRank.Packet := ⟨24*t+21,0,2*q⟩
  have hEA0 := BB6.Agent2EFirstAPacket.exceptional_EA_packet t q hq
  have hEA : ObsEq
      (run (BB6.Agent2EFirstAPacket.duration t q)
        (DRegularSource.sourceSection ⟨9*t+10,q,1⟩))
      (packet c.a c.q c.p
        BB6.Agent2AP2PacketBoundary.fixedTail) := by
    simpa [BB6.Agent2EFirstAPacket.sourceStart,
      BB6.Agent2EFirstAPacket.packetOutput,
      BB6.Agent2EFirstAPacket.fixedTail,c,
      BB6.Agent2AP2PacketBoundary.fixedTail] using hEA0
  have hk : 3*ka+3=24*t+21 := by dsimp [ka];omega
  have hr : 3*r+2=2*q := by dsimp [r];omega
  have hshape : packet c.a c.q c.p
        BB6.Agent2AP2PacketBoundary.fixedTail =
      BB6.Agent2AP2PacketBoundary.input ka 0 r := by
    simp [c,ka,r,BB6.Agent2AP2PacketBoundary.input,
      BB6.Agent2AP2PacketBoundary.fixedTail,
      packet,word,hk,hr]
  have hAP2 :=
    BB6.Agent2AP2PacketBoundary.a_p2_packet_reentry ka 0 r
  let a : Nat :=
    2*(4*ka+3+CryptidA.wordInc
      (BB6.Agent2AP2PacketBoundary.words 0 r))+5
  have hfloor : 2 ≤ a := by dsimp [a];omega
  have hendpoint :
      BB6.Agent2AP2PacketBoundary.endpoint ka 0 r =
        BB6.Agent2BoundaryBZero.regularSection a 3 2 := by
    simp [a,BB6.Agent2AP2PacketBoundary.endpoint,
      BB6.Agent2BoundaryBZero.regularSection]
  have hA : ObsEq
      (run (BB6.Agent2AP2PacketBoundary.sourceTime ka 0 r)
        (packet c.a c.q c.p
          BB6.Agent2AP2PacketBoundary.fixedTail))
      (DRegularSource.sourceSection ⟨a,3,2⟩) := by
    rw [hshape,hAP2,hendpoint,regular_eq_source a 3 2 hfloor]
    exact BB6.Padding.cfgEq_refl _
  refine ⟨BB6.Agent2EFirstAPacket.duration t q +
    BB6.Agent2AP2PacketBoundary.sourceTime ka 0 r,
    a,?_,?_⟩
  · exact source_chain
      (BB6.Agent2EFirstAPacket.duration t q)
      (BB6.Agent2AP2PacketBoundary.sourceTime ka 0 r)
      (DRegularSource.sourceSection ⟨9*t+10,q,1⟩)
      (packet c.a c.q c.p BB6.Agent2AP2PacketBoundary.fixedTail)
      (DRegularSource.sourceSection ⟨a,3,2⟩)
      hEA hA
  · exact ⟨hfloor,Or.inl (show (3:Nat) ≠ 0 by decide)⟩

#print axioms ea_q1_residue_canonical

end BB6.Agent37EAResidueCanonical
