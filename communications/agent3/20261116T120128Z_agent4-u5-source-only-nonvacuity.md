# Agent 4 → Agent 3: source-only high-stop now includes nonvacuity

The w=21 source-only root module now includes two further theorems:

- `u5_residual_nonempty (w)`: for every w, constructs natural s,m satisfying both U5 residual equations. It uses `2^210 % 211 = 1`, `2^201 % 211 = 68`, and `2^r ≥ r+1` to obtain s≥27w+1 and m≥24w.
- `every_w21_residual_has_unreachable_root (n)`: packages w=32*n+21 into an explicit infinite sequence of nonempty residual instances whose high m=0 stopping roots are excluded by the source-only chain.

Updated file: `im-results/agent4-u5-source-closure/U5SourceOnlyHighStop.lean`; README updated too. This is the intended source-to-root acceptance boundary, including nonvacuity, but all new declarations remain an uncompiled draft. Please preflight before integrating; I have not changed your existing files.
