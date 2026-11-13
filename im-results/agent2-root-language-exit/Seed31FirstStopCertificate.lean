import Lean.Elab.Tactic.Omega
import Seed31Probe
import OriginalRootChain
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2ThirtyFirstCertificate

open DRegular
open BB6.Agent2ThirtiethRoot
open BB6.Agent2ThirtyFirstProbe

/-- The linear scan returns the first state whose regular successor is
    undefined, unless the requested fuel is exhausted. -/
theorem firstStopAux_sound :
    ∀ (fuel n : Nat) (s : DRegular.L),
      ∃ k,
        (firstStopAux fuel n s).1 = n+k ∧
        k ≤ fuel ∧
        DRegular.run k s = some (firstStopAux fuel n s).2 ∧
        (k < fuel → DRegular.next (firstStopAux fuel n s).2 = none) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n s
      refine ⟨0, ?_, by omega, ?_, ?_⟩
      · simp [firstStopAux]
      · simp [DRegular.run, firstStopAux]
      · intro hk
        omega
  | succ fuel ih =>
      intro n s
      cases hnext : DRegular.next s with
      | none =>
          refine ⟨0, ?_, by omega, ?_, ?_⟩
          · simp [firstStopAux, hnext]
          · simp [DRegular.run, firstStopAux, hnext]
          · intro _
            exact hnext
      | some u =>
          obtain ⟨k,hcount,hbound,hrun,hstop⟩ := ih (n+1) u
          have haux : firstStopAux (fuel+1) n s =
              firstStopAux fuel (n+1) u := by
            simp [firstStopAux, hnext]
          refine ⟨k+1, ?_, by omega, ?_, ?_⟩
          · rw [haux]
            calc
              (firstStopAux fuel (n+1) u).1 = (n+1)+k := hcount
              _ = n+(k+1) := by omega
          · rw [haux]
            simpa [DRegular.run, hnext] using hrun
          · intro hk
            rw [haux]
            exact hstop (by omega)

/-- The block search is sound because every skipped 512-step block is
    kernel-equivalent to DRegular.run, and canonicality is preserved. -/
theorem firstStopBlocks_sound :
    ∀ (fuel n : Nat) (s : DRegular.L),
      DRegular.Canon s →
      ∃ k,
        (firstStopBlocks fuel n s).1 = n+k ∧
        k ≤ 512*fuel ∧
        DRegular.run k s = some (firstStopBlocks fuel n s).2 ∧
        (k < 512*fuel →
          DRegular.next (firstStopBlocks fuel n s).2 = none) := by
  intro fuel
  induction fuel with
  | zero =>
      intro n s hs
      refine ⟨0, ?_, by omega, ?_, ?_⟩
      · simp [firstStopBlocks]
      · simp [DRegular.run, firstStopBlocks]
      · intro hk
        omega
  | succ fuel ih =>
      intro n s hs
      cases hfast : BB6.DRegularFast.fastRun 512 s with
      | none =>
          have hrun512 : DRegular.run 512 s = none := by
            rw [BB6.DRegularFast.fastRun_correct 512 s hs]
            exact hfast
          obtain ⟨k,hcount,hbound,hrun,hstop⟩ :=
            firstStopAux_sound 512 n s
          have hk : k < 512 := by
            by_contra hnot
            have heq : k = 512 := by omega
            subst k
            rw [hrun] at hrun512
            contradiction
          have haux : firstStopBlocks (fuel+1) n s =
              firstStopAux 512 n s := by
            simp [firstStopBlocks, hfast]
          refine ⟨k, ?_, ?_, ?_, ?_⟩
          · rw [haux]
            exact hcount
          · omega
          · rw [haux]
            exact hrun
          · intro hkmax
            rw [haux]
            exact hstop (by omega)
      | some t =>
          have hrun512 : DRegular.run 512 s = some t := by
            rw [BB6.DRegularFast.fastRun_correct 512 s hs]
            exact hfast
          have ht : DRegular.Canon t :=
            BB6.DRegularFast.run_canon 512 s t hs hrun512
          obtain ⟨k,hcount,hbound,hrun,hstop⟩ :=
            ih (n+512) t ht
          have hblock : firstStopBlocks (fuel+1) n s =
              firstStopBlocks fuel (n+512) t := by
            simp [firstStopBlocks, hfast]
          refine ⟨512+k, ?_, ?_, ?_, ?_⟩
          · rw [hblock]
            calc
              (firstStopBlocks fuel (n+512) t).1 = (n+512)+k := hcount
              _ = n+(512+k) := by omega
          · omega
          · rw [BB6.DRegularFast.run_add 512 k s, hrun512]
            rw [hblock]
            simpa using hrun
          · intro hkmax
            rw [hblock]
            exact hstop (by omega)

/-- The thirtieth reentry seed is canonical: a≥2 and q=0,b=0. -/
theorem seed31_canon : DRegular.Canon seed31 := by
  constructor
  · dsimp [seed31, BB6.Agent2AOneBoundary.aUnary]
    omega
  · right
    rfl

/-- If the bounded probe returns before its cap, it has found the exact
    first regular-language exit, not merely a state sampled at that time. -/
theorem firstExceptionFromSeed31_sound
    (hbound : firstExceptionFromSeed31.1 < 1024000) :
    DRegular.run firstExceptionFromSeed31.1 seed31 =
        some firstExceptionFromSeed31.2 ∧
      DRegular.next firstExceptionFromSeed31.2 = none := by
  obtain ⟨k,hcount,hboundK,hrun,hstop⟩ :=
    firstStopBlocks_sound 2000 0 seed31 seed31_canon
  have hk : k < 512*2000 := by
    have hk0 : k < 1024000 := by
      simpa [firstExceptionFromSeed31,hcount] using hbound
    omega
  constructor
  · simpa [firstExceptionFromSeed31,hcount] using hrun
  · simpa [firstExceptionFromSeed31,hcount] using hstop hk

/-- Conditional source lift of the first exceptional state after the
    thirtieth blank-root reentry. Once the probe bound is discharged, this
    gives an authentic original-machine blank prefix to that exact exit. -/
theorem blank_thirty_first_prefix
    (hbound : firstExceptionFromSeed31.1 < 1024000) :
    ∃ T22 Tnorm24 Tnorm27,
      ObsEq
        (CryptidBoundary.run
          (reentry30Time T22 Tnorm24 Tnorm27 +
            DRegular.accumulated firstExceptionFromSeed31.1 seed31)
          CryptidBoundary.blank)
        (DRegularSource.sourceSection firstExceptionFromSeed31.2) := by
  obtain ⟨T22,Tnorm24,Tnorm27,hroot⟩ :=
    BB6.Agent2ThirtiethRoot.blank_thirtieth_reentry
  have hfirst := firstExceptionFromSeed31_sound hbound
  exact ⟨T22,Tnorm24,Tnorm27,
    BB6.Agent25RootChain.extend_regular
      CryptidBoundary.blank
      (reentry30Time T22 Tnorm24 Tnorm27)
      firstExceptionFromSeed31.1 seed31 firstExceptionFromSeed31.2
      seed31_canon hfirst.1 hroot⟩

#print axioms firstStopAux_sound
#print axioms firstStopBlocks_sound
#print axioms seed31_canon
#print axioms firstExceptionFromSeed31_sound
#print axioms blank_thirty_first_prefix

end BB6.Agent2ThirtyFirstCertificate
