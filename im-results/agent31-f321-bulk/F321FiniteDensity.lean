import F321Periodicity

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31F321Density

/-- Finite number of complete terminal-parameter residue classes, modulo
    4^n, that pass the sound depth-n exclusion test. -/
def acceptedResidueCount (n:Nat) : Nat :=
 ((List.range (2^(2*n))).filter (residuePass n)).length

/-- An exhaustive *kernel-computed* identity, without native_decide or
    native-code trust axioms. These are entire arithmetic progressions,
    by F321Periodicity.residuePass_periodic; the finite cutoff is explicit
    in F321Periodicity.residue_class_never. -/
theorem accepted_depth4 : acceptedResidueCount 4 = 210 := by decide

/-- 898 of the 1024 terminal residue classes are proven impossible beyond
    d >= 6*2^5-3; hence the finite-depth-n=5 kernel theorem excludes
    a set of natural density exactly 898/1024 among candidate terminal
    parameters. The overall machine orbit remains undecided. -/
theorem accepted_depth5 : acceptedResidueCount 5 = 898 := by decide

#print axioms accepted_depth4
#print axioms accepted_depth5
end BB6.Agent31F321Density
