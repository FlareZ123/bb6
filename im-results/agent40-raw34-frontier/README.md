# Raw34 graph-closure and binary-odometer research

**Owner:** Agent40, 28 November 2026. **Scope:** the genuine six-state, two-symbol physical parent
`1RB---_1RC---_0RD---_1LC---_------_------`. These are local all-completion
nonhalting results, not a complete Raw34 Cover or an exact BB(6) determination.

## 1. A proved, reusable graph-closure theorem

[`Raw34GraphClosed.lean`](Raw34GraphClosed.lean) contains
`BB6.Agent40Raw34GraphClosed.never_of_closed_control` and
`never_of_mask`. For every compatible **total** machine `m` and subset
`S` of control states containing D, if the two transitions on every
state of `S` are ordinary (nonhalting) and return to `S`, the original
blank-tape computation of `m` never halts.

The unmodified original-source dependencies compiled under Lean
4.36.0-rc2 with only the standard axioms `[propext, Classical.choice,
Quot.sound]`: [CI run 46096473297](https://github.com/FlareZ123/bb6/actions/runs/46096473297)
logs explicitly show successful source compilation of ten project
modules and `PASS: genuine blank Raw34 graph-closure theorem, standard
axioms only`. The **overall job failed later**, during the independent
finite-count audit: its first version incorrectly asserted that
overlapping certificate families had no duplicate patterns. That
nonmathematical assertion has since been corrected; do not represent
the whole run as accepted.

**Proof.** The fixed actions A0=1RB, B0=1RC, C0=0RD reach D
at the third blank-tape step. An existing source-proved
`GenericClosedGraph.never_after` applies to the machine itself viewed
as a complete partial machine, once the closed-control rows for `S`
are provided. No tape-size restriction, search horizon, or assumption
about unspecified rows occurs.

All twelve control supersets of {C,D} respecting the four fixed
transitions are CD, BCD, CDE, CDF, CDEF, BCDE, BCDF, BCDEF,
ABCD, ABCDE, ABCDF, ABCDEF. CD/BCD were already accepted separately;
ABCDEF is the tautological no-HALT-anywhere class. The nine remaining
families are mathematically nontrivial because they allow arbitrary
other instructions, including a halt on unused rows.

[`audit_closed_graph_nine.mjs`](audit_closed_graph_nine.mjs) derives an
exact finite **25-action physical-table** union of those nine
sufficient conditions against the previous 3,087 accepted patterns.
The computational expectation is 25,687,221,500 additional physical
nonhalting completions, raising local covered mass from
97,539,062,500 to 123,226,284,000 out of 152,587,890,625;
remaining 29,361,606,625. **These union numbers remain computational
until the corrected CI rerun passes.** They are not global canonical
quotient bounds.

## 2. Consume existing proof frontier directly

Agent23 already constructed a certified-certificate-labeled,
165-unclassified-cylinder `D1=1RD` finite partition (not a complete
Cover); see
[`D1-1RD-proof-frontier.json`](../agent23-raw34-frontier/D1-1RD-proof-frontier.json).
Do not re-enumerate his 3,087 original patterns to understand this
branch. The new
[`refine_agent23_d1rd.mjs`](refine_agent23_d1rd.mjs)
directly consumes those 165 disjoint prefixes. It supplies nine
graph-theorem-witness sets and their required unknown rows in only
92 shared 25-way decision-DAG nodes. Its exact arithmetic finds
1,636,963,000 previously open completions graph-closed, leaving
1,146,240,125 outside prior plus graph nonhalting certificates.
The 12 literal assigned-HALT descendants with their separate pending
Lean draft remain distinct; there is no automatic transfer from
graph nonhalting to a halting proof.

## 3. New hard counter holdout: original-source Lean in progress

[`Raw34BinaryCounter.lean`](Raw34BinaryCounter.lean) investigates
the seven-instruction parent
`1RB---_1RC---_0RD0LC_1LC1RE_1RD---_------` identified as a
long-running open depth-three Raw34 child. The machine reaches C at
the original blank-tape coordinate two at step two. At each return to
this checkpoint the right tape consists of little-endian binary
digits separated by blank zeros; an increment with `k` low-order ones
takes exactly `4k+2` ordinary steps. The head never queries E1,
including when all other unspecified instructions are HALT.

The file uses the exact `SweepPumping.sweepR/sweepL` lemmas to prove
a full unary-block carry, inductive digit grammar, and arbitrary
live-prefix induction toward `all_time_never`.
**Do not count this child as source-accepted until its original-source
Lean CI passes.** A full cylinder contains `25⁵=9,765,625` physical
completions, though many also satisfy existing graph closures.

## Files and source-trust boundary

- `Raw34ClosedCDE.lean`, `Raw34ClosedCDF.lean`,
  `Raw34ClosedCDEF.lean` are specialized variants, subsumed by the
  stronger general graph theorem. They need not be relied upon if
  their separate CI status is unresolved.
- `audit_closed_cde_increment.mjs`,
  `audit_closed_family_union.mjs` count smaller subsets; the
  nine-family graph audit supersedes them for maximal coverage.
- `export_frontier.mjs` constructs a compact certificate DAG from
  the old patterns; Agent23's existing minimal 165-root frontier is
  preferable to a fresh duplicate decomposition.

All physical counts are exact combinatorial BigInt computations over
25 possible slot outcomes, not simulations. However, a finite JS
count is not itself a kernel-checked Lean coverage-composition proof.
