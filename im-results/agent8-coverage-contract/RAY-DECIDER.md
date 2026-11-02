# Monotone fresh-ray certificates for BB(6) sparse enumeration

Agent 8, 2026-11-02. **Intermediate proof infrastructure; no new resolved
holdout, BB(6) upper bound, or exact BB(6) value.** These criteria are elementary
and have not been checked for novelty against the wider literature.

## Source-checked all-time theorem

The original `Frontier.lean` semantics has a bi-infinite tape, six control
states, and one halting outcome plus 24 ordinary outcomes per transition slot.
A `PartialMachine` distinguishes a genuinely unassigned outer `none`
from an assigned halting inner `none`. The `Cover` predicate accepts only
fully justified universal leaves or all 25 children of an assigned branch.

For a direction d, let S be any subset of states containing the blank start A.
For every state s in S, require that the scanned-zero transition is already
assigned, moves in direction d, and goes to a member of S. Writes are arbitrary.
By induction, at time n the head is at position n for d=R (respectively −n
for L), the entire as-yet-unvisited ray is blank, and the control state
remains in S. Thus the head always reads zero and can never halt.

- `RayClosed.lean`: the fully quantified infinite-tape proofs
  `rightClosed_leaf`, `leftClosed_leaf`, and a genuine two-state right-sweep
  example that writes ones behind the head.
- `RayChecker.lean`: `rayMaskCheck_sound`, giving a kernel-verified
  `Cover (DecidedBelow B) p` from an accepted six-bit mask.
- `RayOracle.lean`: `rayOracle_sound` searches all 64 subsets in both
  directions and produces the same real proof object.

The criterion also applies *after* a finite, precisely checked trace:
`RayEntry.lean` proves `right_entry_leaf` and `left_entry_leaf`.
Its hypotheses require each transition consulted before step k to be assigned
in the sparse table and an exact full-configuration witness at step k. The
state is in a closed sweep set and the entire future half-tape is blank.
Prefix preservation transports the entry and closed tail to **every**
compatible machine, making these genuine all-time cylinder certificates.

The concrete `RayTurnExample.lean` uses exactly A0=0RB, B0=1LC,
C0=1LC, leaving all other 9 slots free. The head moves right one step,
returns to the original position at step 2, and then sweeps left across
fresh blank tape, writing ones forever. Its initial transition conflicts
with the eventual sweep direction, so this example lies outside the
zero-entry oracle's acceptance condition. The theorem
`turn_example_certificate` certifies all completions with a valid
`Cover.leaf`.

## Exact full-table census for zero-entry rule

For the six scanned-zero slots, and one fixed direction, let k be the
number of distinct control states before the deterministic zero-successor
path first repeats. There are
`(5)_(k-1) × k × 2^k × 25^(6-k)`
matching zero-slot tables: order the k−1 new successors among the five
states different from A, choose a return target among k visited states,
choose each visited state's write bit, and choose arbitrary transitions on
the remaining 6−k states. Summing over k=1,...,6 yields:

```text
k                      1          2         3         4       5       6
term            19531250   15625000   7500000   2400000  480000   46080
sum = 45,582,330 zero-slot tables per direction
```

All scanned-one slots remain unrestricted, contributing `25^6`. Right
and left classes are disjoint because A0 cannot move in both directions.

```text
Per-direction full canonical tables: 11,128,498,535,156,250
Both-direction union:             22,256,997,070,312,500
All six-state 25-choice tables:   59,604,644,775,390,625
Fraction:                         37.341044736%
```

The standalone CommonJS BigInt `ray_count.cjs` independently checks
this formula against a finite successor-path dynamic program, using
`4n+1` canonical choices for an n-state generalization, n=1,...,6.
This census itself is computationally checked, **not** a formal Lean
combinatorial theorem. It counts very easy classes among all raw full
tables, **not** an unresolved-holdout rate, a TNF leaf percentage,
or a quantitative advance toward universal BB(6) coverage.

## Reproduction and audit

The existing **manual-only** `agent8-coverage-contract.yml` workflow
checks unmodified `Frontier.lean`, then all the modules above with
Lean 4.36.0-rc2. [CI run 41505998296](https://github.com/FlareZ123/bb6/actions/runs/41505998296),
source commit `6d9741747a6a77f0ea3090bdb512545ccd40d66b`,
**succeeded**. Its original-source job logs specifically report
`rayOracle_sound`, `right_entry_leaf`, `left_entry_leaf`,
`turn_example_certificate` with axioms exactly
`[propext, Quot.sound]`, no `sorryAx`.
No per-commit workflow is installed. Existing Agent4 cross-model adapters
permit future porting to Agent13's canonical 25-choice representation.

The remain­ing global gap is a complete checked
`Cover (DecidedBelow B) emptyTable` over all six-state machines,
plus an attainable maximal-runtime witness. These new leaves help build
such a certificate but do not supply it.
