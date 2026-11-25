# Raw139 D1=0LE / E1=1LF coverage

**Source-accepted base:** original Lean 4.36.0-rc2 verification at [run 45722158374](https://github.com/FlareZ123/bb6/actions/runs/45722158374), source f03aba072dbed070f4c41866e07e8c0cfa1d5254, artifact 15072239376. The base exact seven-hole parent is `1RB---_1RC---_1LD---_---0LE_---1LF_------`, first-use prefix B0=1RC, C0=1LD, D1=0LE, E1=1LF. The theorem `BB6.Agent41Raw139Small.parent_contract` bounds every compatible halting table by weighted score 512 or retains its exact residual cylinder. This is a local parent contract, not a global BB6 upper bound.

The four continuation edges F0=1LD, D0=1LA, B1=0RC, C1=0RB retain 75 earlier open siblings and certify 17 side-cycle siblings. At the three-hole E0 parent, 163 translated cycles, 116 last-hole leaves, and 15 finite automata reductions leave six one-hole cylinders. The accepted E0 contract has residual completion mass 150 of 15625; the entire parent has 81 residuals and residual mass 4793672025 of 6103515625. The halt sibling at each split is charged at its actual query time plus possible incoming blank delay. Maximum last-hole time is 321.

## All-time sweep closure (new proof candidate)

The remaining machine `1RB0LC_1RC0RC_1LD0RB_1LA0LE_1LA1LF_1LD---` admits two exact families in the original head-relative zipper with current cell included in the left list:
- P=0001, Q=1011, K=0100 (near-head first).
- X(n,h)=D at h, left 1 P^n 0, right 1.
- Y(n,h)=D at h, left 1 P^n 001, right 1.
- X(n,h) -> Y(n+1,h+2) in 12n+18 primitive moves.
- Y(n,h) -> X(n+1,h+2) in 12n+14 primitive moves.
- Hence X(n,h) -> X(n+2,h+4) in 24n+44 moves.
- Authentic blank start reaches X(3,10) at step 102.

The macro lemmas, two sweeps, recurrence, authentic seed, and arbitrarily long sparse runs compiled locally against the exact copied zipper definitions. `Raw139E0OneLA.lean` imports the repository's original `SparseZipper`, lifts those runs through its `zrun_sound` bridge, and proves all completions of F1 never halt. `Raw139SmallPlus.lean` removes only this exact table from both accepted residual lists using a reusable semantic filter theorem. **Source acceptance of the new two modules is pending**. If accepted, five E0 leaves remain (125 raw completions); the complete parent retains 80 residuals.

Remaining E0 base tables are listed in witness-data.json. One of the remaining five is the separately identified upstream Cryptids nonhalting machine; its source bridge is not part of this finite audit.

## Reproduction

- Raw139SmallAudit.lean: accepted partial-audit theorem and explicit finite certificate tree.
- generate.mjs and witness-data.json: deterministic witness discovery and machine-readable base roster. The generator tries recovered 2-, 3-, and 8-state FAR automata on timeouts, and extends the cycle window for two exact linear-drift cases. Generator output is not the proof boundary.
- Raw139E0OneLA.lean: new all-time sweep proof using original-source zipper.
- Raw139SmallPlus.lean: exact-table removal from the two accepted rosters.
- .github/workflows/agent41-raw139-small.yml: manual source-closure compile and axiom audit.

Earlier failed run 45721906157 exposed the reserved Lean identifier `prefix` in the concrete instantiation; the generic soundness proof had already compiled. The successful base run supersedes that failure.
