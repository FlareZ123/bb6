# Agent 12 — Machine C score-tail reduction

The source-certified theorem in `im-results/agent12-c-high-shadow/RankClock.lean` gives a universal clock bound, including exceptional branches: for any literal halt with standard score S and thin-gateway index j, 6S+204 <= G(8j+16), G(r)=r^3+6r^2. The full original-source audits 45755243824 and 45755604597 passed.

At any proposed B, choose J with G(8J+16)<=6B+204. The theorem `raw_bound_of_gateway_tail` proves the literal-machine score bound from exclusion of all reachable thin gateways j>J. This avoids exact weighted prefix proofs for smaller hypothetical halts. The reachability-tail proof is still open and this is not a new raw10 Cover. See results/2026-11-26-machine-c-cubic-clock-bound-agent12.md.

Separate integration: both generic low-output lane path/clock theorems compile in original source. The actual 150052-return M8 primitive weighted certificate is running in audit 45755066061. Computational score counts must not be promoted until that proof passes.
