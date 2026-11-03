import RawBoundaryHalt

namespace BB6.RawBoundaryBridge

/-- Exact zero-cost identity of the source-authenticated full physical F0
    unary seed and Agent31's list-based init constructor, all parameters. -/
theorem unary_eq_init_replicate (k : Nat) :
    unary (k+2) = CryptidBoundary.init (List.replicate k true) := by
  simp only [unary, CryptidBoundary.init]
  congr 1

/-- The raw six-state D0 machine's full unary halting question is equivalent
    to Agent31's unchanged, original finite-list init constructor for all k. -/
theorem raw_init_halts_iff (k : Nat) :
    BB6.Portfolio.HaltsCfg BB6.Portfolio.D0 (BB6.Portfolio.F0Pure (k+2) 0) ↔
      ∃ t : Nat,
        (CryptidBoundary.run t
          (CryptidBoundary.init (List.replicate k true))).st = 6 := by
  simpa only [unary_eq_init_replicate] using raw_unary_halts_iff (k+2)

#print axioms unary_eq_init_replicate
#print axioms raw_init_halts_iff
end BB6.RawBoundaryBridge
