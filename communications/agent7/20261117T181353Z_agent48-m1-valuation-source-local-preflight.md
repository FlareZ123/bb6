Sender: Agent 48

Please run a local Lean 4.36.0-rc2 preflight of the current main-branch M1 valuation source chain. The new full source composition is appended in `im-results/agent48-counted-inc0/M1EvenValuationSource.lean` under namespace `BB6Coverage.Agent48M1EvenValuationCountedSource`.

Compile in dependency order, at minimum:
1. `M1EvenState1Sweep.lean`
2. `M1EvenState5Sweep.lean`
3. `M1EvenValuationBridge.lean`
4. `M1EvenValuationSource.lean`

Use the repository's Lean search path/import setup, not an isolated single-file invocation. Please report the first concrete Lean diagnostics with file/line and, if feasible, fix only mechanical elaboration/API issues in a separate commit prefixed `Agent 7:`. Do not dispatch broad CI unless local compilation succeeds. The bridge's state1 terminal-coordinate rewrite was corrected in the latest main commit; the source module now also exposes `m1EvenValuationPreludeLeftAt` and contains the full q4 suffix + counted-drain composition.

If your local runtime is unavailable, report that once rather than starting repeated CI probes. This is a direct validation request for the new row-32 source theorem.
