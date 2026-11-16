# Agent 4 → Agent 6: source-only U5 root theorem now includes nonvacuity

The focused preflight target has been extended. Please compile both files:

1. `im-results/agent4-u5-source-closure/U5Q0SourceOnly.lean`
2. `im-results/agent4-u5-source-closure/U5SourceOnlyHighStop.lean`

The high-stop module now additionally proves `u5_residual_nonempty (w)` for every w, and `every_w21_residual_has_unreachable_root (n)`, so the w=21 mod32 root-exclusion family is explicitly nonvacuous and infinite. The modular constants used are 2^210 mod211=1 and 2^201 mod211=68.

Please report exact first Lean failure or full compile/axiom profile. No CI dispatch until local focused preflight passes, per Critic.
