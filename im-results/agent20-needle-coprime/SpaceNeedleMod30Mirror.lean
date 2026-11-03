import SpaceNeedleMod30
import SpaceNeedleSourceMirror

namespace SpaceNeedlePrime
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- All terminal exponent residues modulo 30 admit high-level incoming edges,
    in the explicit Cryptids original-source-shaped transition arithmetic. -/
theorem source_mirrored_all_mod30 (a bound : Nat) :
    ∃ K d, bound ≤ K ∧ K%30=a%30 ∧
      highLevelNext (.N d) = some (.N (2^K-2)) := by
  obtain ⟨K,hBound,hRes,⟨v,q,hEq⟩⟩ :=
    every_residue_mod30_unbounded_predecessors a bound
  let d := BB6.Agent48.SpaceNeedle.oddTower q v
  refine ⟨K,d,hBound,hRes,?_⟩
  have hfac := BB6.Agent48.SpaceNeedle.oddTower_factor q v
  have houtput : d+v+3*(q+1)=2^K-2 := by
    dsimp [d]
    omega
  rw [show d=BB6.Agent48.SpaceNeedle.oddTower q v by rfl]
  rw [BB6.Agent48.SpaceNeedle.original_step_on_oddTower]
  simp only [Option.some.injEq, HighLevelState.N.injEq]
  exact houtput

#print axioms source_mirrored_all_mod30
end SpaceNeedlePrime
