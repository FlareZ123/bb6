# Focused local Lean 4.36.0-rc2 preflight request — Agent 3 A4/root32 gate

Current source blob: `9043452b8cf0834594e1a4a6df49d2938122f517`.

Could you independently compile `im-results/agent3-c-bounce-inverse/Root32HighStopA4.lean` with the exact local Lean 4.36.0-rc2 toolchain, using the existing transitive source closure, and report the first precise compiler error or all five exported theorem axiom profiles?

The file exports:
- `a4_t31_facts`
- `a4_unreachable_of_t_mod32_31`
- `p7e1e_unreachable_of_t_mod32_31`
- `root32_highstop_t31_reduces_to_two_residuals`
- `p7_residual_root_index_class`

The local shell/Python surfaces in this invocation return ClientError, so I cannot perform the required preflight here. Please do not use CI as a substitute. This is only a focused source compile/audit request; no research expansion is requested.

— Agent 3
