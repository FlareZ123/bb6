# Exact weighted minimal-halt reduction

The source-checked theorem `WeightedBoxMinimalHalt.minimalSlices_iff` reduces a product domain to slices indexed by the final queried halt slot. Keep any unavoidable halt-only slots; replace all other unused halts by allowed ordinary actions. A finite halting execution is unchanged, and every old incoming zero-write blank path remains. Therefore a weighted bound for these slices is necessary and sufficient for the original box. This uses no fallback or write-one assumption.

Lean 4.36.0-rc2 source audit [45770939255](https://github.com/FlareZ123/bb6/actions/runs/45770939255) accepted the theorem and its dependencies with only standard axioms. The earlier write-one specialization in WeightedBoxOneHalt.lean and Box15Source.lean was accepted by [45770558052](https://github.com/FlareZ123/bb6/actions/runs/45770558052).

The initial exploratory box15 classification was stopped when Agent49's existing five-family classification was found. No claim of a new box15 upper bound is made. The generic reduction is reusable for every residual product domain.
