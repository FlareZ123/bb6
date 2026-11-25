# Block forward FAR and symbolic sweep certificates

The block-FAR approach groups the tape into finite blocks and proves exact primitive execution for every successful block exit. A finite left DFA and right NFA supply an inductive invariant at all block entries. All original-machine transfers concern the exact partial table, so an unreachable hole may be completed arbitrarily. The checker is independent of Coq decider trust.

## Reusable Lean components

- `BlockMacro.lean`: width-three block execution, progress, and primitive prefix safety.
- `BlockFAR.lean`, `RangeCheck.lean`: inductive automaton checking, with bounded kernel chunks.
- `SparseBlockFAR.lean`: equivalent sparse lookup; left-state minimization reduces large certificates.
- `BlockMacro2.lean`, `BlockFAR2.lean`, `RangeCheck2.lean`: two-cell checker sharing width-three primitive semantics, checked concretely for q600.
- `BlockFARBridge.lean`: exact transfer into `BB6Coverage.PartialMachine` and `NeverHalts`.
- `generate_multi.py` and `specialize.py`: untrusted certificate synthesis; Lean checks the finite proof obligations.

The existing manual workflow `.github/workflows/agent5-q0-held-blockfar.yml` supports compact and width-two generation, optional reflection, exact original-table equality, source-semantic coverage, and the dedicated q3500 symbolic proof. It rejects sorryAx/native_decide and uploads generated source and compiled modules.

## Held queue leaves

| Leaf | Exact partial table | Status |
|---|---|---|
| q2800/100 | `1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---` | Concrete width-three candidate verified locally (220 left states, 142 right nodes, 317 edges); existing raw10 complement consumer supplies source integration. |
| q3500 | `1RB0RC_1LC1RD_---1RB_0LD0RE_1LE0LF_1RA1LF` | [Original source accepted](https://github.com/FlareZ123/bb6/actions/runs/45603499126). Symbolic solid growth recurrence. |
| q600 | `1RB1LE_1RC0RD_1LB0RE_1RF0LE_0LA0LB_---0RA` | [Original source accepted](https://github.com/FlareZ123/bb6/actions/runs/45604475251). Width 2, cap 2, modulus 4, runs 2, reflection. |
| q2700 | `1RB0LD_1LC1RA_1LE1LA_---0RB_1RE0RF_1RF0LC` | [Original source and encoded subtraction accepted](https://github.com/FlareZ123/bb6/actions/runs/45604482036). Compact width 3, cap 2, modulus 4, runs 5. |
| q0 | `1RB1RD_1RC0LD_0LA0RE_1LA1LB_0RF---_0LA1RA` | [Original source accepted](https://github.com/FlareZ123/bb6/actions/runs/45605504334). Compact width 3, cap 2, modulus 2, runs 5. |

### q3500 exact growth

`Q03500Sweep.lean` establishes `solid_grows`: a B configuration scanning the right-hand blank after a solid block of 9k+1 ones returns after a strictly positive number of steps to the same form with 9(k+1)+1 ones. The blank computation enters solid(1). Let S(p,a,s) denote F scanning the left zero of a sandwich with p ones on the left, a ones between the zeros, and s ones to the right. The exact successive forms are:

```
solid(9k+1) -> S(0,9k,2) -> S(3k,0,6k+2) -> S(0,9k+2,2)
 -> S(1,9k+3,2) -> S(3k+2,0,6k+4) -> S(0,9k+6,2)
 -> S(3k+2,0,6k+6) -> solid(9k+10).
```

`Q03500Consumer.lean` transfers prefix safety to every completion and supplies `Cover (DecidedBelow B)` for arbitrary B. The exported axiom profiles are only propext and Quot.sound. All 25 C0 completions are nonhalting. Encoded raw10 row: [8,10,11,16,0,8,13,18,19,21,4,23].

### q2700 encoded raw10 refinement

`Raw10Q2700EncodedConsumer.lean` derives the exact row [8,13,11,4,19,3,0,6,20,22,24,9], checks parent inclusion and disjointness from the 66 existing encoded cylinders, and proves exact subtraction with `subtractMany_exact`. All 25 D0 completions are nonhalting. Earlier source-path failures were repaired by copying the source into Lean's root directory. The previous 41-box residual of mass 90,737,503,713,725 becomes 49 boxes of mass 90,737,503,713,700 in independent computational replay; those box count and mass figures are diagnostics, not a separate kernel cardinality result.

## Raw110

All 16 candidates in `Raw110Candidates.json` were locally kernel-checked. The reflected child12/21 minimized left DFA has 168 states instead of 429, with 339 right nodes, 441 edges, two accepting zero states and 465 active row checks. The remaining child5/161 and 5/790 have the shared deterministic macro orbit in `CarryMacro.lean` and `CarryEquivalence.lean`. Agent7 subsequently obtained a complete original-source raw110 parent proof in [run 45597857116](https://github.com/FlareZ123/bb6/actions/runs/45597857116); use that parent certificate rather than count our individual leaves twice.

These are intermediate local cylinders and reusable checkers. They do not establish the global Busy Beaver upper bound.
