import Seed24956SecondReentry
import EChainDoubleBReentry
import DRegularSourceShift
import ExceptionalESafeCanonical
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 100000000

namespace BB6.Agent2Seed24956FamilySecondReentry

open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent2Seed24956SecondReentry

/-- The reset cylinder k=81*r+61, Q=0, with a two-one suffix. -/
def familyResetPacket (r : Nat) : CryptidBoundary.Cfg :=
  BB6.Agent31PacketSource.packet (3*(81*r+61)+4) 0 2
    (false::List.replicate 6 true)

/-- Exact source time for the P2 reset, one E-chain step, two B edges,
    and the final A-marker closure in the k=81*r+61 cylinder. -/
def familyResetTime (r : Nat) : Nat :=
  BB6.Agent2PacketP2Reset.eTwoTime (81*r+61) 0 +
    BB6.Agent37EChain.chainTime 1 (54*r+41) 0 +
    BB6.Agent37EChainDoubleBReentry.bTwiceTime (64*r+48) +
    BB6.Agent35MarkerA.aTime0 (4096*r+3117) 0 1

/-- The exact regular section produced by the preceding source chain. -/
def familyResetEndpoint (r : Nat) : DRegular.L :=
  ⟨32768*r+24956,2,2⟩

/-- Reuse the source-section normalization needed by the A-marker endpoint. -/
private theorem regularSection_sourceSection
    (a q b : Nat) (ha : 2 ≤ a) :
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
  have heq : BB6.Agent37EChainDoubleBReentry.endpointZero n =
      BB6.Agent2BoundaryBZero.regularSection (n+1) 2 2 := by
    simp [BB6.Agent37EChainDoubleBReentry.endpointZero,
      BB6.Agent2BoundaryBZero.regularSection,
      CryptidBoundary.oppairs,hrep,List.append_assoc]
  have hsec := regularSection_sourceSection (n+1) 2 2 (by omega)
  rw [heq,hsec]
  exact BB6.Padding.cfgEq_refl _

theorem familyResetEndpoint_canon (r : Nat) :
    DRegular.Canon (familyResetEndpoint r) := by
  simp [DRegular.Canon, familyResetEndpoint]

/-- Every member of the k=81*r+61, Q=0 P2 reset cylinder returns
    source-observationally to the exact section L(32768*r+24956,2,2).
    This strengthens the concrete r=0 instance to an infinite family. -/
theorem family_reset_source_reentry (r : Nat) :
    ObsEq
      (CryptidBoundary.run (familyResetTime r) (familyResetPacket r))
      (DRegularSource.sourceSection (familyResetEndpoint r)) := by
  let k : Nat := 81*r+61
  let h : Nat := 54*r+41
  let t : Nat := 64*r+48
  let ka : Nat := 4096*r+3117
  have hmarker :
      BB6.Agent2PacketP2Reset.marker = BB6.Agent35K4Shapes.marker := by
    decide
  have hresetRaw :
      CryptidBoundary.run (BB6.Agent2PacketP2Reset.eTwoTime k 0)
        (BB6.Agent31PacketSource.packet (3*k+4) 0 2
          (false::List.replicate 6 true)) =
      BB6.Agent31PacketSource.packet (8*k+5) 0 6
        BB6.Agent35K4Shapes.marker := by
    have hreset := BB6.Agent2PacketP2Reset.e_two_reset k 0
    simpa [hmarker] using hreset
  have hIn : 8*k+5 = 1+4*3*h := by
    simp [k,h]
    omega
  have hOut : 27*t+17 = 1+4*8*h := by
    simp [h,t]
    omega
  have hchainRaw :
      CryptidBoundary.run (BB6.Agent37EChain.chainTime 1 h 0)
        (BB6.Agent31PacketSource.packet (8*k+5) 0 6
          BB6.Agent35K4Shapes.marker) =
      BB6.Agent31PacketSource.packet (27*t+17) 2 3
        BB6.Agent35K4Shapes.marker := by
    have hchain := BB6.Agent37EChain.chain_return 1 h 0 3
      BB6.Agent35K4Shapes.marker (by omega)
    simpa [Nat.pow_one,hIn,hOut] using hchain
  have hka : 64*t+45 = ka := by
    simp [t,ka]
    omega
  have hBRaw :
      CryptidBoundary.run
        (BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
        (BB6.Agent31PacketSource.packet (27*t+17) 2 3
          BB6.Agent35K4Shapes.marker) =
      BB6.Agent31PacketSource.packet (3*ka+3) 0 3
        BB6.Agent35K4Shapes.marker := by
    have hb := BB6.Agent37EChainDoubleBExit.b_twice t 0 3
      BB6.Agent35K4Shapes.marker
    simpa [BB6.Agent37EChainDoubleBReentry.bTwiceTime,hka] using hb
  have hWord :
      CryptidA.wordInc (BB6.Agent35MarkerA.code 0 1) = 4 := by
    decide
  have hn :
      2*((4*ka+3)+CryptidA.wordInc
        (BB6.Agent35MarkerA.code 0 1))+5 = 32768*r+24955 := by
    rw [hWord]
    simp [ka]
    omega
  have hARaw :
      CryptidBoundary.run (BB6.Agent35MarkerA.aTime0 ka 0 1)
        (BB6.Agent31PacketSource.packet (3*ka+3) 0 3
          BB6.Agent35K4Shapes.marker) =
      BB6.Agent37EChainDoubleBReentry.endpointZero (32768*r+24955) := by
    have ha := BB6.Agent35MarkerA.close_zero ka 0 1
    simpa [BB6.Agent37EChainDoubleBReentry.endpointZero,hn] using ha
  have hResetObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent2PacketP2Reset.eTwoTime k 0)
          (familyResetPacket r))
        (BB6.Agent31PacketSource.packet (8*k+5) 0 6
          BB6.Agent35K4Shapes.marker) := by
    change ObsEq
      (CryptidBoundary.run
        (BB6.Agent2PacketP2Reset.eTwoTime k 0)
        (BB6.Agent31PacketSource.packet (3*k+4) 0 2
          (false::List.replicate 6 true)))
      (BB6.Agent31PacketSource.packet (8*k+5) 0 6
        BB6.Agent35K4Shapes.marker)
    rw [hresetRaw]
    exact BB6.Padding.cfgEq_refl _
  have hChainObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent37EChain.chainTime 1 h 0)
          (BB6.Agent31PacketSource.packet (8*k+5) 0 6
            BB6.Agent35K4Shapes.marker))
        (BB6.Agent31PacketSource.packet (27*t+17) 2 3
          BB6.Agent35K4Shapes.marker) := by
    rw [hchainRaw]
    exact BB6.Padding.cfgEq_refl _
  have hBObs :
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
          (BB6.Agent31PacketSource.packet (27*t+17) 2 3
            BB6.Agent35K4Shapes.marker))
        (BB6.Agent31PacketSource.packet (3*ka+3) 0 3
          BB6.Agent35K4Shapes.marker) := by
    rw [hBRaw]
    exact BB6.Padding.cfgEq_refl _
  have hAObs :
      ObsEq
        (CryptidBoundary.run (BB6.Agent35MarkerA.aTime0 ka 0 1)
          (BB6.Agent31PacketSource.packet (3*ka+3) 0 3
            BB6.Agent35K4Shapes.marker))
        (DRegularSource.sourceSection (familyResetEndpoint r)) := by
    rw [hARaw]
    simpa [familyResetEndpoint] using
      endpointZero_sourceSection (32768*r+24955)
  have h01 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k 0)
    (BB6.Agent37EChain.chainTime 1 h 0)
    (familyResetPacket r)
    (BB6.Agent31PacketSource.packet (8*k+5) 0 6
      BB6.Agent35K4Shapes.marker)
    (BB6.Agent31PacketSource.packet (27*t+17) 2 3
      BB6.Agent35K4Shapes.marker)
    hResetObs hChainObs
  have h012 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k 0 +
      BB6.Agent37EChain.chainTime 1 h 0)
    (BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
    (familyResetPacket r)
    (BB6.Agent31PacketSource.packet (27*t+17) 2 3
      BB6.Agent35K4Shapes.marker)
    (BB6.Agent31PacketSource.packet (3*ka+3) 0 3
      BB6.Agent35K4Shapes.marker)
    h01 hBObs
  have h0123 := BB6.BoundaryPadding.source_chain
    (BB6.Agent2PacketP2Reset.eTwoTime k 0 +
      BB6.Agent37EChain.chainTime 1 h 0 +
      BB6.Agent37EChainDoubleBReentry.bTwiceTime t)
    (BB6.Agent35MarkerA.aTime0 ka 0 1)
    (familyResetPacket r)
    (BB6.Agent31PacketSource.packet (3*ka+3) 0 3
      BB6.Agent35K4Shapes.marker)
    (DRegularSource.sourceSection (familyResetEndpoint r))
    h012 hAObs
  simpa [familyResetTime,familyResetPacket,familyResetEndpoint,
    k,h,t,ka,Nat.add_assoc] using h0123

/-- The DRegular shift parameter used to keep the 86-step output in
    the E row: the input family index is r=3^87*s. -/
def shiftP (s : Nat) : Nat := 32768*3*s

/-- E-row parameter after transporting the base 86-step run by shiftP. -/
def shiftedExitK (s : Nat) : Nat :=
  exitK + 8^86*32768*s

theorem shifted_input_eq_family_endpoint (s : Nat) :
    BB6.DRegularSourceShift.inputLift seed24956 86 (shiftP s) =
      familyResetEndpoint (3^87*s) := by
  have hpow : 3^87 = 3^86*3 := by decide
  simp [BB6.DRegularSourceShift.inputLift,
    BB6.DRegularShift.shiftNat, shiftP, familyResetEndpoint,
    seed24956, hpow, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem shifted_output_eq_E_shape (s : Nat) :
    BB6.DRegularSourceShift.outputLift seed24956Exit 86 (shiftP s) =
      (⟨3*shiftedExitK s+4,5,1⟩ : DRegular.L) := by
  have hbase :
      107283033157493534200791430928221345342090 =
        3*exitK+4 := by
    decide
  simp [BB6.DRegularSourceShift.outputLift,
    BB6.DRegularShift.shiftNat, shiftP, shiftedExitK,
    seed24956Exit, exitK, hbase,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- The 86-step source run is stable under the 3^86/8^86 DRegular
    shift. Choosing p=32768*3*s makes both the input reset index and
    the output E-exit index land in the required arithmetic families. -/
theorem shifted_regular_source_run (s : Nat) :
    ObsEq
      (CryptidBoundary.run
        (DRegular.accumulated 86 (familyResetEndpoint (3^87*s)))
        (DRegularSource.sourceSection (familyResetEndpoint (3^87*s))))
      (DRegularSource.sourceSection ⟨3*shiftedExitK s+4,5,1⟩) := by
  have h :=
    (BB6.DRegularSourceShift.paired_original_run
      seed24956 seed24956Exit 86 (shiftP s)
      seed24956_canon seed24956_run86).2
  simpa [shifted_input_eq_family_endpoint,
    shifted_output_eq_E_shape] using h

theorem shifted_safe_E_exit (s : Nat) :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run T
          (DRegularSource.sourceSection ⟨3*shiftedExitK s+4,5,1⟩))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨T,a,q,b,h,hcanon⟩ :=
    BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
      (shiftedExitK s) 5 (by omega) (by omega)
  refine ⟨BB6.Agent32EAll.duration (shiftedExitK s) 4 + T,
    a,q,b, ?_,hcanon⟩
  simpa using h

/-- An infinite subfamily of P2 reset packets has a second source return:
    k=81*3^87*s+61, Q=0. The reset chain reaches a 3^87-shift of
    L(24956,2,2); 86 DRegular steps reach a q=5 E exit, and safe-E
    closure returns to a canonical section. This is a prepared-packet
    theorem, not a blank-tape reachability claim. -/
theorem family_reset_second_reentry (s : Nat) :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run
          (familyResetTime (3^87*s) +
            DRegular.accumulated 86 (familyResetEndpoint (3^87*s)) + T)
          (familyResetPacket (3^87*s)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨T,a,q,b,hSafe,hcanon⟩ := shifted_safe_E_exit s
  have h01 := BB6.BoundaryPadding.source_chain
    (familyResetTime (3^87*s))
    (DRegular.accumulated 86 (familyResetEndpoint (3^87*s)))
    (familyResetPacket (3^87*s))
    (DRegularSource.sourceSection (familyResetEndpoint (3^87*s)))
    (DRegularSource.sourceSection ⟨3*shiftedExitK s+4,5,1⟩)
    (family_reset_source_reentry (3^87*s))
    (shifted_regular_source_run s)
  have h012 := BB6.BoundaryPadding.source_chain
    (familyResetTime (3^87*s) +
      DRegular.accumulated 86 (familyResetEndpoint (3^87*s)))
    T
    (familyResetPacket (3^87*s))
    (DRegularSource.sourceSection ⟨3*shiftedExitK s+4,5,1⟩)
    (DRegularSource.sourceSection ⟨a,q,b⟩)
    h01 hSafe
  exact ⟨T,a,q,b, by simpa [Nat.add_assoc] using h012, hcanon⟩

#print axioms family_reset_source_reentry
#print axioms shifted_regular_source_run
#print axioms family_reset_second_reentry

end BB6.Agent2Seed24956FamilySecondReentry
