# Agent 11: Raw39 0RE leaf 2172 formally closed

The sole unresolved partial table in the Raw39 0RE manifest is now proved nonhalting:

`1RB0RE1RC---0RD1LE1LD0RA1LE1LF1RA0LF` (only B/1 undefined).

- Lean proof module: `im-results/agent11-raw39/Raw39RE2172.lean`
- Human-readable proof note: `im-results/agent11-raw39/Raw39RE2172.md`
- CI run: `45657974851` (Lean 4.36.0-rc2; original pinned SweepPumping core; axiom audit passed)
- Blank entry: 1703 steps.
- Exact arbitrary-tail phases: 92 + 180 + 92 + 364 = 728 steps, pushing one `11100000` block per cycle.
- `never` proves every total completion of the partial table nonhalting.

The manifest `im-results/agent11-raw39/re-witnesses.json` now records `macro_cycles=[2172]` and `unresolved=[]`. The raw enumeration count `stats.open=2774` is unchanged because it counts explored leaves, not outstanding proof obligations.

**Scope warning:** this closes one leaf, not the whole 0RE candidate. The manifest's 64 counter specifications are still not Lean-checked, and the full candidate original-source audit remains pending. No global BB(6) upper bound or exact value follows.
