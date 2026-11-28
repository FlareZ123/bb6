import Q0148EpochConnect
import Q0148EpochGlue

namespace BB6.Agent5Q0148NeverCover
open BB6Coverage BB6Coverage.Agent31Pump
open BB6.Agent5Q0148BoundarySweep BB6.Agent5Q0148EpochConnect BB6.Agent39Q0148Carry

set_option maxHeartbeats 400000

theorem reset1_source : Reset1 := by
  intro us n
  refine ⟨a1FirstTime us.reverse n + (2*(2*n)+6),by omega,?_⟩
  simpa [resetA1Frame] using a1_reset_to_train us n [] []

theorem reset3_source : Reset3 := by
  intro us n
  refine ⟨(((a3FirstTime (us.reverse ++ [n]) +
    a3SecondTime (us.reverse ++ [n])) + a3ThirdTime (us.reverse ++ [n])) +
    (2*(2*n)+6)),by omega,?_⟩
  simpa [resetA3Frame] using a3_reset_to_train us n [] []

theorem high_source : HighTrain := by
  intro n ns R
  have h := highTrainFromFirst_source n ns [] R
  dsimp only at h
  exact ⟨_,h⟩

theorem low_source : LowTrain := by
  intro n mid u v R
  have h := lowTrainFromFirst_source n mid u v [] R
  dsimp only at h
  rw [← low_first_state_split (mid.length+1) n mid u v [] R] at h
  exact ⟨_,h⟩

/-- The original q0-148 F1-open table's whole completion family,
provided the imported exact source sweeps are kernel certified. -/
theorem never_cover : Cover NeverHalts p :=
  cover_of_source_train reset1_source reset3_source high_source low_source

#print axioms never_cover
end BB6.Agent5Q0148NeverCover
