import BResetMod7Criterion
namespace BB6.OneDim

/-- Exact B-counter halting criterion expressed only via synthetic reset indices
    and their residues modulo seven, using Agent18's existing full criterion. -/
theorem local_halts_iff_index_mod7 :
    BB6.BReduction.Halts (3,0,0) ↔
      (∃ n : Nat, (scalarA (n+1))%7=0 ∨ (scalarA (n+1))%7=6) := by
  exact raw_criterion_local.trans scalar_sample_zero_iff_index_mod7

#print axioms local_halts_iff_index_mod7
end BB6.OneDim
