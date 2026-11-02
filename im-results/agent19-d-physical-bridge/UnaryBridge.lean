import SourceIntegration
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19.Physical
open BB6.Padding (Config bitAt)
open BB6.Portfolio (Cfg State)

/-- A finite source tape with n unary marks to the right of a state-F head. -/
def sourceUnary (n : Nat) : CryptidBoundary.Cfg :=
  ⟨[],false,List.replicate n true,5⟩

private theorem bitAt_replicate_true (n j : Nat) :
    bitAt (List.replicate n true) j = decide (j < n) := by
  by_cases hj : j < n <;> simp [bitAt,List.getElem?_replicate,hj]

/-- The two independent formalisms represent literally the same infinite
    physical unary F-section, including the infinite blank extension. -/
theorem unary_realize (n : Nat) :
    realize (boundarySafe (sourceUnary n) (by simp [sourceUnary]) 0) =
      BB6.Portfolio.F0Pure n 0 := by
  simp only [realize,boundarySafe,sourceUnary,
    BB6.BoundaryPadding.represent,encode,BB6.Portfolio.translateCfg,
    BB6.Portfolio.F0Pure,Int.sub_zero,Int.zero_add]
  congr 1
  funext i
  by_cases hi0 : i=0
  · subst i
    simp [tape]
  · by_cases hineg : i<0
    · have hnot : ¬(0<i ∧ i≤(n:Int)) := by omega
      simp [tape,hi0,hineg,hnot]
    · have hipos : 0<i := by omega
      simp only [tape, if_neg hi0, if_neg hineg]
      rw [bitAt_replicate_true]
      have idx : ((i-1).toNat<n) ↔ (0<i ∧ i≤(n:Int)) := by omega
      by_cases hh : ((i-1).toNat < n)
      · have hj := idx.mp hh
        simp [hh,hj] <;> omega
      · have hj : ¬(0<i ∧ i≤(n:Int)) := by
          intro hyp
          exact hh (idx.mpr hyp)
        simp [hh,hj] <;> omega

/-- Exact undefined-run comparison for each physical unary F-section seed. -/
theorem unary_run_none_iff_source_frozen (n t : Nat) :
    BB6.Portfolio.run BB6.Portfolio.D0 t
      (some (BB6.Portfolio.F0Pure n 0)) = none ↔
        (CryptidBoundary.run t (sourceUnary n)).st = 6 := by
  have h := raw_run_none_iff_boundary_frozen t (sourceUnary n)
    (by simp [sourceUnary]) 0
  rw [unary_realize] at h
  exact h

/-- All-time halting equivalence for any unary seed, independent of n. -/
theorem unary_halts_iff_source_frozen (n : Nat) :
    BB6.Portfolio.HaltsCfg BB6.Portfolio.D0
      (BB6.Portfolio.F0Pure n 0) ↔
        ∃ t, (CryptidBoundary.run t (sourceUnary n)).st = 6 := by
  have h := physical_halts_iff_boundary_halts (sourceUnary n)
    (by simp [sourceUnary]) 0
  rw [unary_realize] at h
  exact h

#print axioms unary_run_none_iff_source_frozen
#print axioms unary_halts_iff_source_frozen
#print axioms unary_realize
end BB6.Agent19.Physical
