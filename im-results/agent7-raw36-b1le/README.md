# Raw36 D1=1LB, B1=1LE (index 16)

**Candidate complete; full source acceptance pending.** Literal parent `1RB---_1RC1LE_0RD---_0LD1LB_------_------`, first-use cut 5. Candidate weighted bound 387.

Fast canonical scan: 844969 nodes, 35207 splits, 587316 cycles, 27632 FAR, 193812 last, 1002 OPEN, 229019 halting choices. All 1002 OPEN now have exact literal witnesses: 353 FAR, 487 ngram, 128 RLE, 28 affine sweeps, 1 whole-stack modular, 2 SAT-synthesized BiDFA, 3 periodic-phase. All 621 stack-based candidates replay and compress via the active inverse-stack relation; Lean source gate underway. No global roster change.

## Reproduce

- Use original `agent29-raw36/canonical_search.cjs` (parent, 5, tree) or the accelerated `scan_tree.cpp`, with the original canonical bank (`candidate.json.codes`, 101230333, 101023202, prior agent7-raw36-transfer fixture code column, unique in order). The scan emits metadata and a separate JSON tree as its optional fourth argument; join metadata with tree under key tree.
- Sorted raw literal keys (underscores removed, joined with newline, no trailing newline) SHA256: `12a61d5f27011e721ac8128854e107f9ec9388a1ba0e8a9385714c3c02622d01`.
- `evidence.json.xz.b64`: base64+XZ JSON, bound 387, digest and exact sorted witness data. Tags f=FAR code, n=window width/count, r=run count/cap/modulus/count, s=affine sweep recipe, m=prefix/modulus/base/count, d=explicit left/right DFA, p=periodic prefix/period/type/mask/initial/count.
- `python generate_cover.py tree.json output` emits 39 TwoSidedAutomata modules, seven sweep modules, base, 24 child audits, and parent. Compile the base, stack and sweep modules before children and parent. Uses original accepted source modules `CanonicalPrefixFast`, `Raw36Cut`, `TwoSidedAutomata`, `SweepPumping`. Local dependencies were taken from accepted artifacts 15241456595 and 15121597506 (common module objects byte-identical).
- The C++ scanner and Python generators are untrusted discovery tools. Kernel checks enforce every cycle, FAR, stack invariant, exact literal and weighted halting case; no native_decide or sorry. A successful source gate must establish `BB6.Agent29Raw36B116.cover : Cover (WeightedBound 387) b1`.

Earlier `far.tsv.gz.b64` and `winners.txt.gz.b64` are saved transfer-only intermediate witnesses. The compact all-1002 bank supersedes them.

## New phase abstraction

The paired-bit modular period-3 certificate resolves `1RB---_1RC1LE_0RD0RF_0LD1LB_0LA1LD_0LE0RF`. Two period-4 fixed-one phase certificates resolve `1RB---_1RC1LE_0RD0RE_0LD1LB_0LF0RE_0LA1LD` and `1RB---_1RC1LE_0RD1RB_0LD1LB_0LF0RE_0LA1LD`. The stack summary preserves allowable residue-phase sets and a short literal prefix; active predecessor edges then enforce transition closure. The methods are general candidate generators; the independent stack theorem proves the resulting finite invariants.
