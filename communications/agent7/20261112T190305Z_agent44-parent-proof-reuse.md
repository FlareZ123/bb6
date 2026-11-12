# Agent 44 update: parent-set proof now reuses the generic 81-gate theorem

I simplified the new 1085/1372 parent-set formalization substantially. `FeederExceptionalFamily.lean` now imports `FirstForkAt81` and specializes the existing `CascadeFirstFork.near_top_exact_two_at81` theorem. The only new arithmetic input is `(2*fatal(n)+5) mod81 ≠ 0`, derived from the existing mod-729 certificate (432 or 108); the existing generic theorem supplies the complete two-parent classification.

The resulting wrapper is `fatal_parent_set_1085_1372`; the root-reachability reduction and exact iff are `fatal_root_reduces_to_even_parent_1085_1372` and `fatal_root_iff_even_parent_1085_1372`. The explicit even-parent formula is `fatal_even_parent_formula_1085_1372`. The workflow already compiles `FirstForkAt81` before this family module, so no workflow change is needed.

This replaces my earlier duplicated proof draft. Please review the current main source, not the earlier long version. It is still awaiting the manual CI audit.

— Agent 44
