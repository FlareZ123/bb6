# Raw45: sharp 96-step maximum for a five-hole six-state family

**28 November 2026 — Agent 24. Source-certified local exactness.**

## Main theorem

Consider the partial six-state two-symbol machine

```text
1RB0LC_1RC0LA_0RD---_1LD1RB_------_------
```

where every `---` is a genuinely unspecified transition. For **every**
fully specified completion compatible with these seven fixed ordinary
transitions, starting on the blank tape in state A:

> If the machine halts, it does so after **at most 96 steps**,
> counting its final halting transition.

There is an explicitly given compatible machine which halts on its
**96th step**. Consequently **96 is the exact maximum ordinary
blank-tape halting score of this entire five-hole family**.

The family contains (25^5=9,765,625) completed six-state tables,
with a total choice at each undefined row of 24 ordinary moves or
one final halting instruction. This is a *local exact maximum*.
It is dramatically below the published global six-state Busy Beaver
lower bound and **does not determine BB(6)**, eliminate all of
the seven-hole Raw45 parent, or remove its global Canonical40
representative.

The upper and attaining lower-bound proofs have both passed the
original-source Lean 4.36.0-rc2 compiler and axiom gate:

- **Universal upper bound:** [sharded source kernel and axiom run
  46093481756](https://github.com/FlareZ123/bb6/actions/runs/46093481756);
  theorem `BB6.Agent24Raw45FullChild.weighted_bound` in
  [Raw45CutAssembled.lean](../im-results/agent24-raw45/Raw45CutAssembled.lean).
- **Lower bound 96:** [source kernel and axiom run
  46092079569](https://github.com/FlareZ123/bb6/actions/runs/46092079569);
  theorem `BB6.Agent24Raw45Sharp96.halts_after_95` in
  [Raw45Sharp96Witness.lean](../im-results/agent24-raw45/Raw45Sharp96Witness.lean).

The independently written combined theorem
[Raw45Exact96.lean](../im-results/agent24-raw45/Raw45Exact96.lean)
states both universal upper and exact attainment inside one formal
declaration; its independent original-source gate is tracked separately.
The mathematical exactness claim above uses the **two already
source-accepted proofs** and the unconditional fact that every
six-state machine's zero-writing incoming-delay graph includes the
length-zero path from state A to itself.

## Certificate structure and exhaustiveness

The source theorem's `Audit` decision tree contains **11,449
nodes**, partitioned into:

| Audit node type | Count | Soundness mechanism |
|---|---:|---|
| Ordinary first-hole split | 477 | All 24 ordinary move choices, plus the halting alternative checked by the source weighted-query bound |
| Translated half-line cycle | 8,834 | Exact blank-tape prefix, exact positive period and preserved infinite half-line |
| Final single unassigned transition | 2,068 | Source weighted first-hole query bound |
| Local-window nonhalting proof | 68 | Checked sparse n-gram finite abstract closure |
| Nonhalting growth induction | 2 | Exact arbitrary-length alternating word-packet recurrence |

At the root the first undefined transition is C1 (state C
scanning 1) at ordinary time 8. The explored descendants have
maximum first-hole query time 95. The source uses the
`zipCheck 96` decision tree checker to verify every leaf
and branch, and `certifiedZip` to obtain a quantified
`WeightedBound 96 m` for an **arbitrary total machine**
compatible with the parent. The source does not trust
a search program's answer. In particular the 8,834 cycle
leaves were checked within the Lean kernel; they are not
a finite-run nonhalt guess.

The full, larger source is retained as
[Raw45B1LA_A1LC_FullCut.lean](../im-results/agent24-raw45/Raw45B1LA_A1LC_FullCut.lean).
For tractable original-source kernel reduction and auditable logs,
the accepted modular version factors eight heavy first-level branches
into `Raw45CutPart04.lean`, `05`, `10`, `11`,
`16`, `17`, `22`, `23`, and sixteen shorter
branches into `Raw45CutAssembled.lean`. The exact literal
parent is [Raw45CutBase.lean](../im-results/agent24-raw45/Raw45CutBase.lean).
No trusted external SAT solver, external candidate witness,
or additional axioms are introduced.

## Two hard one-hole exceptions

The only depth-five residuals not closed by a translated cycle
or sparse local-window certificate are E/F-conjugate one-hole machines:

```text
1RB0LC_1RC0LA_0RD1RE_1LD1RB_1LF---_0LA0LF
1RB0LC_1RC0LA_0RD1RF_1LD1RB_0LA0LE_1LE---
```

Both have formal source proofs that **every** compatible completion
runs forever. Starting from the blank tape, after exactly 45
ordinary steps they enter a family of configurations indexed
by (n\in\mathbb N), with alternating sections:

```text
odd(n)  --8n+24 steps--> even(n)
even(n) --8n+28 steps--> odd(n+1)
```

The two phases have head state E (or its conjugate F), and
right words built from three-bit tokens `001` and `010`
and unary tails. The exact two-sweep section-return cost is
`16n+52`, which is strictly positive for all n. The
proof uses exact primitive multi-step identities with arbitrary
unmodified tape suffixes, arbitrary-length `sweepL`/
`sweepR` induction and `never_of_growth`. All the
remaining undefined instruction rows are genuinely arbitrary.

Source and accepted CI:
[hard L1](../im-results/agent24-raw45/Raw45B1LA_A1LC_L1Growth.lean),
[run 46091372018](https://github.com/FlareZ123/bb6/actions/runs/46091372018);
[hard L2](../im-results/agent24-raw45/Raw45B1LA_A1LC_L2Growth.lean),
[run 46091554966](https://github.com/FlareZ123/bb6/actions/runs/46091554966).

The other 68 abstract closures are
[Raw45B1LA_A1LC_NGram68.lean](../im-results/agent24-raw45/Raw45B1LA_A1LC_NGram68.lean),
accepted by source+axiom
[run 46091283707](https://github.com/FlareZ123/bb6/actions/runs/46091283707).

## Sharp halting witness

A fully specified compatible table attaining score 96 is

```text
1RB0LC_1RC0LA_0RD0LE_1LD1RB_0LF---_1RF0RA
```

The row E1 is the **halting instruction**. The other
eleven rows are ordinary moves. Lean proves from the true
blank configuration that the machine has 95 ordinary transitions
before querying E1, so that the final halt is instruction
number **96**, via the source `HaltsAfter witness 95` theorem.
It additionally proves `0 ∈ delays (zeroNext witness) 0`
and `¬WeightedBound 95 witness`; the latter establishes
weighted sharpness as well as ordinary blank-time sharpness.
There is a second E/F-conjugate 96-step witness.

## Separation from the global BB(6) problem

This exact local maximum says nothing about an unexamined
completion of a *different* partial family. In particular
the seven-hole Raw45 parent
`1RB---_1RC---_0RD---_1LD1RB_------_------`
has many remaining unclassified descendants outside this
five-hole child, so its own Cover and the larger Canonical40
global maximality hypotheses **remain open**. Related,
but disjoint, certified Raw45 nonhalting descendants are
reported in
[159 finite cycles and six growth families](2026-11-28-raw45-159-cycles-six-growth-agent24.md).

The value 96 is an attainable **maximum over the 9,765,625
compatible six-state tables in this local cylinder**, not
the global Busy Beaver value.
