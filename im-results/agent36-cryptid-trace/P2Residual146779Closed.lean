import Lean.Elab.Tactic.Omega
import EZTwoK0BRegular
import P2Residual146779Source

/-! Compose the exact original-machine k146779 prepared trace into the new
 E/p2 Z3 k≡0 (mod3), positive-q regularization family. -/
namespace BB6.Agent36EZTwoBZero
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent2BoundaryBZero BB6.BoundaryPadding

/-- Previously unresolved prepared source k=146779, Q=0, fixed-tail
    exception, fully original-machine resolved by exact guarded
    normalizer, two marker transformations, and the new E/p2 Z family.
    No genuine blank-root claim. -/
theorem k146779_original_regular :
    ∃ T a q b,
      ObsEq
        (run T
          (packet 440341 0 2
            (false :: List.replicate 6 true)))
        (regularSection a q b) := by
  obtain ⟨T0,h0⟩ :=
    BB6.Agent36Residual146779.residual_source
  have hk : 2879299338241 = 3*(3*319922148693)+4 := by decide
  have hq : 8=7+1 := by decide
  obtain ⟨T1,a,q,b,h1⟩ :=
    e_two_Z_k0_regular 319922148693 7 3
  refine ⟨T0+T1,a,q,b,?_⟩
  have h1' : ObsEq
      (run T1
        (packet 2879299338241 8 2
          (BB6.Agent2MarkerZero.marker 3)))
      (regularSection a q b) := by
    simpa only [←hk,←hq] using h1
  exact source_chain T0 T1
    (packet 440341 0 2
      (false::List.replicate 6 true))
    (packet 2879299338241 8 2
      (BB6.Agent2MarkerZero.marker 3))
    (regularSection a q b)
    (by rw [h0]; exact BB6.Padding.cfgEq_refl _) h1'

#print axioms k146779_original_regular
end BB6.Agent36EZTwoBZero
