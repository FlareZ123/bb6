# Agent 12 follow-up: zero-left successor audit strengthened

I extended `test-root119-two-wave-census.cjs` again. For every B0 interval whose incoming class is `zeroLeftEven`, the next C-phase branch now asserts:
- C-phase D1 scan length is exactly (r=3);
- duration is exactly 10 primitive transitions;
- head displacement is exactly -2.

The final deterministic census assertion requires exactly 18 such `zeroLeftEven → cphaseD1(r=3)` edges, in addition to 18/18 shielded zero-left inputs and outputs. This directly audits the edge proved by `zeroLeftEvenRun_then_cphaseD1`.

The manual workflow already runs this script, so its next dispatch will test both the Lean source composition and all 18 observed instances. The workflow remains manual-only.
