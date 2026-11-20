import Seed24956SecondReentry
import D3SecondReturnAlignment
import EChainDoubleBReentry
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 100000000

namespace BB6.Agent2Seed24956Depth3SecondReentry

open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent31PacketSource
open BB6.Agent2Seed24956SecondReentry
open BB6.Agent37D3SecondReturnAlignment

/-- The depth-three P2 reset packet aligned to the 86-step seed. -/
def d3ResetPacket (v : Nat) : CryptidBoundary.Cfg :=
  packet (3*familyK v+4) 3 2 (false::List.replicate 6 true)

/-- P2 reset, three E calls, two B calls, and the A-marker completion. -/
def d3ResetTime (v : Nat) : Nat :=
  BB6.Agent2PacketP2Reset.eTwoTime (familyK v) 3 +
    BB6.Agent37EChain.chainTime 3 (familyH v) 0 +
    BB6.Agent37EChainDoubleBReentry.bTwiceTime (familyT v) +
    BB6.Agent35MarkerA.aTime0 (familyKA v) 4 1

/-- Exact regular section at the end of the depth-three reset route. -/
def d3Endpoint (v : Nat) : DRegular.L :=
  ⟨familyEndpoint v,2,2⟩

private theorem regularSection_sourceSection (a q b : Nat) (ha : 2 ≤ a) :
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
      rw [← List.cons_append]
      rw [← List.replicate_succ]
  have hrep : List.replicate a true =
      [true,true] ++ List.replicate (a-2) true := by
    rw [show a = 2+(a-2) by omega, hrepAdd]
    simp
  rw [hrep]
  simp [List.append_assoc]

private theorem endpointZero_sourceSection (n : Nat) :
    ObsEq (BB6.Agent37EChainDoubleBReentry.endpointZero n)
      (DRegularSource.sourceSection ⟨n+1,2,2⟩) := by
  have hrep : List.replicate (n+1) true =
      List.replicate n true ++ [true] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp [List.replicate_succ,ih,List.append_assoc]
  have heq :
      BB6.Agent37EChainDoubleBReentry.endpointZero n =
        BB6.Agent2BoundaryBZero.regularSection (n+1) 2 2 := by
    simp [BB6.Agent37EChainDoubleBReentry.endpointZero,
      BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs,hrep,List.append_assoc]
  have hsec := regularSection_sourceSection (n+1) 2 2 (by omega)
  rw [heq,hsec]
  exact BB6.Padding.cfgEq_refl _

/-- The depth-three P2/E/B/B/A source path reaches the exact aligned
    section L(24956+3^87*(1315608+2^21*v),2,2). This is a prepared-packet
    statement; it does not assert blank-root reachability. -/
theorem d3_reset_source_reentry (v : Nat) :
    ObsEq
      (CryptidBoundary.run (d3ResetTime v) (d3ResetPacket v))
      (DRegularSource.sourceSection (d3Endpoint v)) := by
  have hmarker :
      BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
    decide
  have hprefix :
      8*familyK v+5 = 1+4*3^3*familyH v := by
    calc
      8*familyK v+5 = 4*(2*familyK v+1)+1 := by omega
      _ = 4*(3^3*familyH v)+1 := by
        rw [reset_3adic_alignment]
      _ = 1+4*3^3*familyH v := by omega
  have hresetRaw :
      CryptidBoundary.run (BB6.Agent2PacketP2Reset.eTwoTime (familyK v) 3)
        (d3ResetPacket v) =
      packet (8*familyK v+5) 0 12 BB6.Agent35K4Shapes.marker := by
    have h := BB6.Agent2PacketP2Reset.e_two_reset (familyK v) 3
    simpa [d3ResetPacket,hmarker] using h
  have hchainRaw :
      CryptidBoundary.run (BB6.Agent37EChain.chainTime 3 (familyH v) 0)
        (packet (8*familyK v+5) 0 12 BB6.Agent35K4Shapes.marker) =
      packet (27*familyT v+17) 6 3 BB6.Agent35K4Shapes.marker := by
    rw [hprefix]
    have h := BB6.Agent37EChain.chain_return 3 (familyH v) 0 3
      BB6.Agent35K4Shapes.marker (by dsimp [familyH]; omega)
    simpa [E_chain_BB_index] using h
  have hBraw :
      CryptidBoundary.run
        (BB6.Agent37EChainDoubleBReentry.bTwiceTime (familyT v))
        (packet (27*familyT v+17) 6 3 BB6.Agent35K4Shapes.marker) =
      packet (3*familyKA v+3) 4 3 BB6.Agent35K4Shapes.marker := by
    have h := BB6.Agent37EChainDoubleBExit.b_twice (familyT v) 4 3
      BB6.Agent35K4Shapes.marker
    simpa [BB6.Agent37EChainDoubleBReentry.bTwiceTime,
      familyKA] using h
  have hWord :
      CryptidA.wordInc (BB6.Agent35MarkerA.code 4 1) = 8 := by
    decide
  have hN :
      2*((4*familyKA v+3)+
        CryptidA.wordInc (BB6.Agent35MarkerA.code 4 1))+5 =
        8*familyKA v+27 := by
    rw [hWord]
    omega
  have hAraw :
      CryptidBoundary.run (BB6.Agent35MarkerA.aTime0 (familyKA v) 4 1)
        (packet (3*familyKA v+3) 4 3 BB6.Agent35K4Shapes.marker) =
      BB6.Agent37EChainDoubleBReentry.endpointZero
        (8*familyKA v+27) := by
    have h := BB6.Agent35MarkerA.close_zero (familyKA v) 4 1
    simpa [BB6.Agent37EChainDoubleBReentry.endpointZero,hN] using h
  have hResetObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent2PacketP2Reset.eTwoTime (familyK v) 3)
          (d3ResetPacket v))
        (packet (8*familyK v+5) 0 12 BB6.Agent35K4Shapes.marker) := by
    rw [hresetRaw]
    exact BB6.Padding.cfgEq_refl _
  have hChainObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent37EChain.chainTime 3 (familyH v) 0)
          (packet (8*familyK v+5) 0 12 BB6.Agent35K4Shapes.marker))
        (packet (27*familyT v+17) 6 3 BB6.Agent35K4Shapes.marker) := by
    rw [hchainRaw]
    exact BB6.Padding.cfgEq_refl _
  have hBObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent37EChainDoubleBReentry.bTwiceTime (familyT v))
          (packet (27*familyT v+17) 6 3 BB6.Agent35K4Shapes.marker))
        (packet (3*familyKA v+3) 4 3 BB6.Agent35K4Shapes.marker) := by
    rw [hBraw]
    exact BB6.Padding.cfgEq_refl _
  have hAObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent35MarkerA.aTime0 (familyKA v) 4 1)
          (packet (3*familyKA v+3) 4 3 BB6.Agent35K4Shapes.marker))
        (DRegularSource.sourceSection (d3Endpoint v)) := by
    rw [hAraw]
    have hN' :
        8*familyKA v+27+1 = familyEndpoint v := by
      dsimp [familyEndpoint]
      omega
    simpa [d3Endpoint,hN'] using
      endpointZero_sourceSection (8*familyKA v+27)
  have h01 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime (familyK v) 3)
    (BB6.Agent37EChain.chainTime 3 (familyH v) 0)
    (d3ResetPacket v)
    (packet (8*familyK v+5) 0 12 BB6.Agent35K4Shapes.marker)
    (packet (27*familyT v+17) 6 3 BB6.Agent35K4Shapes.marker)
    hResetObs hChainObs
  have h012 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime (familyK v) 3 +
      BB6.Agent37EChain.chainTime 3 (familyH v) 0)
    (BB6.Agent37EChainDoubleBReentry.bTwiceTime (familyT v))
    (d3ResetPacket v)
    (packet (27*familyT v+17) 6 3 BB6.Agent35K4Shapes.marker)
    (packet (3*familyKA v+3) 4 3 BB6.Agent35K4Shapes.marker)
    h01 hBObs
  have h0123 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime (familyK v) 3 +
      BB6.Agent37EChain.chainTime 3 (familyH v) 0 +
      BB6.Agent37EChainDoubleBReentry.bTwiceTime (familyT v))
    (BB6.Agent35MarkerA.aTime0 (familyKA v) 4 1)
    (d3ResetPacket v)
    (packet (3*familyKA v+3) 4 3 BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection (d3Endpoint v))
    h012 hAObs
  simpa [d3ResetTime,d3ResetPacket,Nat.add_assoc] using h0123

/-- The 86-step DRegular orbit from the base seed lifts to the depth-three
    endpoint by the exact 3^86/8^86 affine shift. -/
theorem d3_shifted_regular_source_run (v : Nat) :
    ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated 86 (d3Endpoint v))
        (DRegularSource.sourceSection (d3Endpoint v)))
      (DRegularSource.sourceSection
        ⟨3*shiftedExitK v+4,5,1⟩) := by
  have hin :
      BB6.DRegularSourceShift.inputLift seed24956 86 (packetShift v) =
        d3Endpoint v := by
    simp only [BB6.DRegularSourceShift.inputLift,
      BB6.DRegularShift.shiftNat, seed24956, d3Endpoint]
    congr 1
    exact (input_shift_for_86_steps v).symm
  have hout :
      BB6.DRegularSourceShift.outputLift seed24956Exit 86 (packetShift v) =
        ⟨3*shiftedExitK v+4,5,1⟩ := by
    simp only [BB6.DRegularSourceShift.outputLift,
      BB6.DRegularShift.shiftNat, seed24956Exit]
    congr 1
    simpa [baseExitA] using (transported_exit_shape v)
  have h :=
    (BB6.DRegularSourceShift.paired_original_run
      seed24956 seed24956Exit 86 (packetShift v)
      seed24956_canon seed24956_run86).2
  rw [hin,hout] at h
  exact h

/-- The shifted q=5 exit is in the universal source-certified safe-E
    class and returns to a canonical DRegular section. -/
theorem d3_shifted_safe_E_exit (v : Nat) :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run T
          (DRegularSource.sourceSection ⟨3*shiftedExitK v+4,5,1⟩))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨T,a,q,b,h,hcanon⟩ :=
    BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
      (shiftedExitK v) 5 (by omega) (by omega)
  refine ⟨BB6.Agent32EAll.duration (shiftedExitK v) 4 + T,
    a,q,b,?_,hcanon⟩
  simpa using h

/-- Every member of the depth-three P2 cylinder has a second
    source-certified return to a canonical regular section. The theorem
    remains conditional on its prepared packet and is not a blank-root
    reachability result. -/
theorem d3_family_second_reentry (v : Nat) :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run
          (d3ResetTime v +
            DRegular.accumulated 86 (d3Endpoint v) + T)
          (d3ResetPacket v))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨T,a,q,b,hSafe,hcanon⟩ := d3_shifted_safe_E_exit v
  have h01 := BB6.BoundaryPadding.source_chain
    (d3ResetTime v)
    (DRegular.accumulated 86 (d3Endpoint v))
    (d3ResetPacket v)
    (DRegularSource.sourceSection (d3Endpoint v))
    (DRegularSource.sourceSection ⟨3*shiftedExitK v+4,5,1⟩)
    (d3_reset_source_reentry v)
    (d3_shifted_regular_source_run v)
  have h012 := BB6.BoundaryPadding.source_chain
    (d3ResetTime v + DRegular.accumulated 86 (d3Endpoint v))
    T
    (d3ResetPacket v)
    (DRegularSource.sourceSection ⟨3*shiftedExitK v+4,5,1⟩)
    (DRegularSource.sourceSection ⟨a,q,b⟩)
    h01 hSafe
  exact ⟨T,a,q,b,by simpa [Nat.add_assoc] using h012,hcanon⟩

#print axioms d3_reset_source_reentry
#print axioms d3_shifted_regular_source_run
#print axioms d3_shifted_safe_E_exit
#print axioms d3_family_second_reentry

end BB6.Agent2Seed24956Depth3SecondReentry
