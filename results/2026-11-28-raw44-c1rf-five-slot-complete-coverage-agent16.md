# Source-certified five-unassigned-slot Raw44 C1=0RF Cover

**Status: original-source Lean accepted.** [Complete workflow run 46126770939](https://github.com/FlareZ123/bb6/actions/runs/46126770939), on commit [282e5fef](https://github.com/FlareZ123/bb6/commit/282e5fefbd8e6be91a3fb096af3da3107b8d1a0e), compiled the generated original six-state, two-symbol Lean proof closure. The decisive repair is [ba0a3da](https://github.com/FlareZ123/bb6/commit/ba0a3daad9a521d76315e9874fdf3d0b36482592).

## Exact theorem and scope

Consider the partial six-state Turing table (A through F; zero/one columns):

| State | On 0 | On 1 |
| --- | --- | --- |
| A | 1RB | ? |
| B | 1RC | 0RC |
| C | 0RD | 0RF |
| D | 1LD | 1LB |
| E | ? | ? |
| F | ? | ? |

All five missing entries take any of 25 standard actions, including the explicit halting action. Thus the cylinder contains **25^5 = 9,765,625 distinct complete machines**.

The Lean declaration **`BB6.Agent16Raw44Cut.weighted_bound`** establishes, for *every* complete machine `m` compatible with that partial parent:

```lean
WeightedBound 211 m
```

Equivalently, every halting compatible machine satisfies the established weighted-first-write score cap 211, and nonhalting machines satisfy the bound vacuously. This is a **local five-slot classification**, not a statement that all these machines halt and not an ordinary-step bound without applying the established weighted/ordinary comparison. The proof uses exact finite cylinders together with symbolic `NeverHalts` certificates.

## Reproducibility and nontrivial symbolic leaf

The source generator [`generate_cut.cjs`](../im-results/agent16-raw44/generate_cut.cjs) emits the exhaustive first-hole tree, its ordinary finite trace and side-cycle cases, width-bounded NGram certificates, and individually proved symbolic exceptions. The successful workflow selector is `raw44-cut-0rf-assembled` in [`agent38-m62-kernel.yml`](../.github/workflows/agent38-m62-kernel.yml), which runs the generator for the `0RF` branch and compiles the complete `Raw44CutAssembled.lean` source with its dependencies, rather than linking opaque generated object files.

One indispensable exception is the **two-hole C1=0RF growth cylinder**. Its partial table was initially miscopied from the C1=0RE sibling: the imported growth theorem compiled in isolation, but the generated original-source parent-child table did not match. The repair explicitly exchanges the E/F state labels in the `Raw44B1RC_C1RF_TwoHoleSwapGrowth.lean` machine *without weakening its exact inductive recurrence*. In particular, the corrected instructions are

```text
C1 = 0RF, E0 = 0RD, E1 = 1RD, F1 = 0RE,
```

with A1 and F0 genuinely unassigned. The whole parent source closure passed after this repair; the earlier failing parent run [46107414625](https://github.com/FlareZ123/bb6/actions/runs/46107414625) should not be cited as accepted.

## Significance and boundary

This establishes one complete original-machine **Raw44 C1=0RF** cylinder, not the full Raw44 parent Cover and not a decrease in the latest Canonical40 global proof's outstanding number. Other C1 instructions remain independent obligations. A logically valid promotion to a global Busy Beaver bound requires source-accepted composition into the exact current parent and the fixed-score representative theorem; simple table counts cannot substitute for that composition.
