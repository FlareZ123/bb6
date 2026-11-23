# Five-step translated-blank drift: 1,200 disjoint nonhalting cylinders

**Scope:** A closed-form six-state, two-symbol **blank-start nonhalting family** and a deterministic, exhaustive independent JavaScript check. The five-step drift argument and the disjointness/counting proof below hold for every specified table and every completion. **Not yet Lean source-compiled and not yet grafted into the depth-four global audit.** In particular, `0.012288%` is the mass of these explicitly described nonhalting cylinders, **not a verified incremental increase** over the published classifier, and no BB(6) upper bound follows. Keep this in `im-results/` until original-source acceptance and evidence of genuinely new coverage.

## 1. Exact five-row family

Denote the blank-start state by `A`. Choose:

- a direction `d ∈ {L,R}`;
- a state `B ∈ {1,…,5}` (different from A);
- any `C ∈ {0,…,5}`;
- a state `D ∈ {0,…,5}\{C}`;
- a state `E ∈ {0,…,5}\{A,B}`.

The letters B,C,D,E below denote *parameters* rather than necessarily the fixed alphabetical labels of those states. Fix five transition inputs:

| Consulted input | Assigned ordinary transition |
| --- | --- |
| `A/0` | write 1, move `d`, enter `B` |
| `B/0` | write 1, move opposite `d`, enter `C` |
| `C/1` | write 0, move `d`, enter `D` |
| `D/1` | write 0, move opposite `d`, enter `E` |
| `E/0` | write 0, move `d`, enter `A` |

The three restrictions guarantee all five consulted input rows are distinct. Their seven unassigned rows can independently take any of 25 ordinary-or-halt actions.

**Theorem (paper-level, directly from physical machine semantics).** Every completion of each such partial table runs forever from the blank tape. If the head starts at position `h` in state A on an entirely zero tape, its five real transitions are:

| Defined moves | State | Head | 1-marked cells |
| ---: | --- | ---: | --- |
| 0 | A | `h` | ∅ |
| 1 | B | `h+d` | `{h}` |
| 2 | C | `h` | `{h,h+d}` |
| 3 | D | `h+d` | `{h+d}` |
| 4 | E | `h` | ∅ |
| 5 | A | `h+d` | ∅ |

The only entries consulted are the five fixed ordinary actions. The fifth configuration is a translated copy of the blank start, with head displacement `d`. Apply the same five-step implication inductively for every `h=kd`. The five listed configurations cover every natural time, and no halt can occur. This argument uses the actual tape symbols, including both read-one entries; following hypothetical zero-only control flow would be invalid.

**Theorem (exact disjointness).** Distinct parameter tuples define transition-incompatible partial tables. If directions differ, their A/0 actions conflict. At equal direction, differing B choices conflict at A/0; at equal B, differing C choices conflict at B/0; at equal B,C, differing D choices conflict at C/1; at equal B,C,D, differing E choices conflict at D/1. Consequently **no full machine can lie in two of these cylinders**.

There are exactly `2·5·6·5·4=1200` parameter tuples. Each fixes 5/12 rows and represents `25^7` full tables. Their disjoint union therefore contains exactly

```text
1200 × 25^7 = 7,324,218,750,000
out of 25^12 = 59,604,644,775,390,625
fraction 1200/25^5 = 1200/9,765,625 = 0.00012288 = 0.012288%.
```

A concrete member for `d=R,` `B=1,C=2,D=3,E=4` fixes `A/0=1RB, B/0=1LC, C/1=0RD, D/1=0LE, E/0=0RA`.

## 2. Reproduction and proof boundary

The dependency-free [`verify_five_step_drift.cjs`](verify_five_step_drift.cjs) constructs **all 1,200** concrete five-row maps, executes their actual five Turing steps on an explicit mutable two-way tape, checks that every tape is blank at the translated return, asserts all partial tables are distinct, and checks all **719,400 unordered pairs** have an assigned-input conflict. It asserts the exact mass and emits the concrete five-step example. Run `node im-results/agent1-five-step-blank-drift/verify_five_step_drift.cjs`. The symbolic proofs above establish the all-completions claims; the bounded computation only audits the 1,200 finite parameter instances, not a separate long machine orbit.

Existing reusable source bridge: [Agent 24's `finiteTranslatedCheck_sound`](../agent24-translated-cycle/TranslatedFiniteOracle.lean) accepts a five-step cycle with `entry=0, period=5` and turns a finite translated-configuration check into a `Cover (DecidedBelow bound)` for **every** completion. The direct Lean acceptance target is a parametric (or 1,200-element finite) theorem that the exact `finiteTranslatedCheck p 0 5` is true, plus the disjointness/mass statement. That proof has **not been compiled in this invocation** because the supplied local runtime returned `ClientError` before executing any shell or Python command; do not label it kernel checked without a compiler result.

This pattern is **different** from Agent 27's accepted five-slot two-mark conveyor (its D/1 writes 1, whereas ours erases 1), and is distinct from Agent 27's candidate 80 three-slot blank drift tables (our first two transitions both write 1, whereas those three-slot schemas have A/0 or B/0 write 0). Their family [dossier](../agent27-three-slot-translated/README.md) separately distinguishes successful source acceptance from uncompiled graft drafts. These distinctions by themselves do *not* establish that our cylinders were absent from other, more general global deciders.

## 3. Missing decisive global-classifier edge

The current depth-four global lasso audit is
`lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4` ([source](../agent32-zero-prefix-global/LassoTraceAudit.lean)). Our five consulted slots appear in the exact physical order A/0, B/0, C/1, D/1, E/0. A depth-four tree therefore reaches the four-row parent and cannot branch on the final E/0 row; the relevant test is whether that parent is *already* accepted by `lassoDecisionOracle` at its actual oracle bounds. If it is open for all 1,200 parents, a proof-carrying `addCertificates` graft would close the full family without changing any unrelated open leaf.

**Still to prove**: the original-source finite-translated-check certificate, exact old-oracle rejection for every four-row parent, the parent's physical-first-unknown path and open preservation, and a validated incremental mass difference against the *existing* frontier. This is substantially stronger than simply counting nonhalting completions and is the next useful target. Also avoid another dedicated CI workflow: use a targeted existing manual source family workflow, after local preflight if available.

No surviving hard-root machine, universal bound, or exact value of BB(6) has been established.
