# Six exact symbolic growth leaves in the coarse Raw11 q0 parents

**Current result:** the first exceptional one-hole cylinder of each of q0 parents 138, 140, 141, 142, 143 and 154 has an exact unbounded growth recurrence from the authentic blank start. The six fixtures were replayed by a separate direct symbolic checker against the literal transition tables, checking every primitive and arbitrary-tail local sweep and the final normalized word equality. The Lean module using the existing source-connected Agent46AutoPump checker is **not yet compiled** in this invocation; no parent or global roster removal follows yet.

| q0 parent | Exact one-hole machine | Blank seed step | Family step | Cost a*n+b |
|---|---|---:|---:|---:|
| 138 | `1RB1LC_1RC0LD_0LA1LA_0RE0RD_---1RF_0RB1RB` | 43 | n→n+2 | 144n+294 |
| 140 | `1RB1LC_1RC0LD_0LA0LB_1RE1LB_0RF---_0RB1RD` | 58 | n→n+1 | 28n+87 |
| 141 | `1RB1LC_1RC0LD_0LA0RB_1LA1RE_1LF---_1RD1RF` | 130 | n→n+1 | 14n+67 |
| 142 | `1RB1LC_1RC0LD_0LA1LB_0RA0LE_1RE0LF_---1RD` | 162 | n→n+1 | 50n+150 |
| 143 | `1RB1LC_1RC0LD_0LA1RB_0RE1LB_1RF---_1LA0RE` | 113 | n→n+1 | 24n+85 |
| 154 | `1RB0LC_1RC0LD_0LA1LA_1RE0RD_1RF---_1RA1LD` | 187 | n→n+2 | 88n+328 |

The simpler paper-level single-return sections (L nearest first excluding scan, R including scan, both zero padded) are:

- **138:** E(blank;1^(6n+5)), recurrence cost 111+72n and n→n+1. See [complete six-local-rule proof](q0-coarse138-sweep.md).
- **140:** B(00(1101)^(n+2);blank), cost 87+28n. The initial 8-step turn reaches D, which transfers one 1101 left block in six steps. A 21-step left boundary reaches E; E transfers each 0001 right block in 22 steps, using two known zeros of lookahead (blank padding is allowed at the last block). Final E0 F0 returns to B. The recurrence increases the number of blocks by one.
- **141:** D(blank;100(10)^(2n+6)1), cost 67+14n. Five-step entry, six-step transfers of 1010 into four left ones, five-step right boundary, four-step transfers of two left ones into an 01 right prefix, three-step left boundary.
- **142:** E(blank;000(10)^(2n+4)1), cost 150+50n. Three-step entry, ten-step right transfers of 1010 into four left ones, 23-step right turn, 20-step left transfers of two left ones to 01 on the right (six ones of lookahead), 24-step terminal left boundary.
- **143:** B(blank;11(01)^(2n+4)), cost 85+24n. Six alternating unary/alternating-word sweeps, with fixed finite turns; exact trace in fixture.
- **154:** A(blank;0101000(100)^(2n+3)101), cost 142+44n. 15-step right transfers of each 100 block, 15-step terminal-101 variant, 23-step right boundary, seven-step left transfers of 001, 17-step blank-left boundary. Two returns are used in the fixture to obtain exact syntactic zipper-word growth including the finite zero padding.

These are all-time statements, not extrapolations. Each fixture uses the exact finite zipper representation from [Agent46AutoPump](../agent46-raw13-cut/Agent46AutoPump.lean), whose left word includes the scanned bit. Its symbolic word is a finite prefix, an arbitrary repeated block, and a suffix (possibly itself periodic). A primitive can read only a known bit. An accelerated sweep must execute a finite local trace without touching either unknown tail, returning to the same state and fixed prefixes and moving one whole block. Induction then transfers an arbitrary number of copies. Exact normalized equality with the family shifted by inc, plus the authentic finite seed and positive cost, implies live prefixes of unbounded length for every compatible completion.

## Reproduce and consume

- [q0-coarse-pumps.json](q0-coarse-pumps.json): six explicit Agent46AutoPump-compatible fixtures. The root metadata is for routing only.
- [verify-coarse-pumps.cjs](verify-coarse-pumps.cjs): direct symbolic replay (not Lean), run with `node verify-coarse-pumps.cjs`. Verifies seed, each local transfer with arbitrary tails, exact family match, cost and positivity. The checker deliberately refuses unknown-bit reads. `--regenerate` repeats the JS port of the existing autoword.py candidate search from the known seed pairs.
- [Raw11Q0CoarsePumps.lean](Raw11Q0CoarsePumps.lean): direct certificate module, imports Agent46AutoPump and Root56Coverage, exports one arbitrary-bound Cover per literal table. Lean 4.36.0-rc2 source/axiom acceptance is pending. This reuses the existing kernel-checkable mechanism instead of constructing a new trusted oracle.

The bank generator stopped at the first unresolved leaf in each parent (138:8480, 140:9201, 141:2884, 142:450, 143:2196, 154:6423 visited nodes). These are not full census counts. Next mathematical task: exhaust each parent search retaining all other uncovered children; use these exact leaf Covers when compiled. A parent count or global cut cannot be inferred from the six leaves.
