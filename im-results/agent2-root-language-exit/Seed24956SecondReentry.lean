import DRegularSourceShift
import EChainDoubleBReentry
import ExceptionalESafeCanonical
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 180000
set_option maxHeartbeats 100000000

namespace BB6.Agent2Seed24956SecondReentry

open CryptidBoundary BB6.BoundaryPadding
open BB6.Agent31PacketSource

/-- The corrected concrete P2-reset source route ends at L(24956,2,2). -/
def seed24956 : DRegular.L := ⟨24956,2,2⟩

/-- Exact DRegular state after 86 regular transitions from L(24956,2,2).
    Its E-exit residue is a ≡ 23638 (mod 59049), q=5, b=1. -/
def seed24956Exit : DRegular.L :=
  ⟨107283033157493534200791430928221345342090,5,1⟩

/-- Since a=3*exitK+4, this is an E-row state in the q=5 safe residue. -/
def exitK : Nat := 35761011052497844733597143642740448447362

theorem seed24956_canon : DRegular.Canon seed24956 := by
  simp [DRegular.Canon, seed24956]

theorem seed24956_run86 :
    DRegular.run 86 seed24956 = some seed24956Exit := by
  decide

theorem seed24956_exit_next_none :
    DRegular.next seed24956Exit = none := by
  decide

theorem seed24956_exit_canon : DRegular.Canon seed24956Exit := by
  simp [DRegular.Canon, seed24956Exit]

theorem seed24956_exit_shape :
    seed24956Exit = (⟨3*exitK+4,5,1⟩ : DRegular.L) := by
  norm_num [seed24956Exit, exitK]

/-- Lift the 86-step DRegular trajectory to the authenticated original
    six-state source machine, with exact accumulated primitive time. -/
theorem seed24956_source_run :
    ObsEq
      (CryptidBoundary.run (DRegular.accumulated 86 seed24956)
        (DRegularSource.sourceSection seed24956))
      (DRegularSource.sourceSection seed24956Exit) := by
  have h := BB6.DRegularSourceShift.lifted_original_run
    seed24956 seed24956Exit 86 0 seed24956_canon seed24956_run86
  simpa [BB6.DRegularSourceShift.inputLift,
    BB6.DRegularSourceShift.outputLift,
    BB6.DRegularShift.shiftNat, seed24956, seed24956Exit] using h

/-- The q=5 E-exit reached from L(24956,2,2) is in the universal
    q>=2, q≠1 (mod 3) safe-E family and returns to a canonical section. -/
theorem seed24956_safe_exit :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run T
          (DRegularSource.sourceSection seed24956Exit))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨T,a,q,b,h,hcanon⟩ :=
    BB6.Agent37ExceptionalESafeCanonical.all_E_safe_reentry_canonical
      exitK 5 (by omega) (by omega)
  exact ⟨T,a,q,b, by
    simpa [seed24956Exit, exitK] using h, hcanon⟩

/-- The concrete P2 reset input therefore has a second source-certified
    return to a canonical DRegular section: reset/B-E-chain-B-B-A to
    L(24956,2,2), 86 regular transitions to a q=5 E exit, then the
    general safe-E source closure. This remains a prepared-packet result,
    not a blank-tape reachability claim. -/
theorem concrete_reset_second_reentry :
    ∃ T a q b,
      ObsEq
        (CryptidBoundary.run
          (BB6.Agent37EChainDoubleBReentry.concreteResetTime +
            DRegular.accumulated 86 seed24956 + T)
          (BB6.Agent31PacketSource.packet 187 0 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection ⟨a,q,b⟩) ∧
      DRegular.Canon ⟨a,q,b⟩ := by
  obtain ⟨T,a,q,b,hSafe,hcanon⟩ := seed24956_safe_exit
  have hReset :
      ObsEq
        (CryptidBoundary.run
          BB6.Agent37EChainDoubleBReentry.concreteResetTime
          (BB6.Agent31PacketSource.packet 187 0 2
            (false::List.replicate 6 true)))
        (DRegularSource.sourceSection seed24956) := by
    simpa [seed24956] using
      BB6.Agent37EChainDoubleBReentry.concrete_reset_double_B_to_A_source_reentry
  have h01 := BB6.BoundaryPadding.source_chain
    BB6.Agent37EChainDoubleBReentry.concreteResetTime
    (DRegular.accumulated 86 seed24956)
    (BB6.Agent31PacketSource.packet 187 0 2
      (false::List.replicate 6 true))
    (DRegularSource.sourceSection seed24956)
    (DRegularSource.sourceSection seed24956Exit)
    hReset seed24956_source_run
  have h012 := BB6.BoundaryPadding.source_chain
    (BB6.Agent37EChainDoubleBReentry.concreteResetTime +
      DRegular.accumulated 86 seed24956)
    T
    (BB6.Agent31PacketSource.packet 187 0 2
      (false::List.replicate 6 true))
    (DRegularSource.sourceSection seed24956Exit)
    (DRegularSource.sourceSection ⟨a,q,b⟩)
    h01 hSafe
  exact ⟨T,a,q,b, by simpa [Nat.add_assoc] using h012, hcanon⟩

#print axioms seed24956_run86
#print axioms seed24956_source_run
#print axioms seed24956_safe_exit
#print axioms concrete_reset_second_reentry

end BB6.Agent2Seed24956SecondReentry
