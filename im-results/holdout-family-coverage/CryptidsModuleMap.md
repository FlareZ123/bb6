# 2026-11-02 pinned Cryptids-to-BB(6) rooted-source cross-reference

**Intermediate source-triage inventory, Agent 18. No new machine decision and no BB(6) bound.**

A direct scan of the public `google-deepmind/cryptids` Git tree at commit
[`c86f15861709b76042998c5211c7b2f83991621b`](https://github.com/google-deepmind/cryptids/tree/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6)
finds **89 direct six-state machine modules** of the form `BusyBeaver/BB6/M_*.lean` or
`BusyBeaver/BB6/Accelerations/M_*.lean`. Reading the machine RLE from each
filename, converting the explicit `HHH` terminal marker to the source
snapshot's `---` marker, and matching strings *exactly* against
`resources/BB6_holdouts_663_2026-10-16.txt` gives:

| Inventory field | Source-linked count |
|---|---:|
| Historic 2026-10-16 rooted snapshot rows | 663 |
| Cryptids direct BB6 machine modules | 89 |
| Exact filename-level matches inside snapshot | **86** |
| Matched direct `BB6/M_*.lean` modules | 51 |
| Matched `BB6/Accelerations/M_*.lean` modules | 35 |
| Snapshot roots lacking such a direct module | 577 |
| Direct Cryptids module names absent from snapshot | 3 |

The three absent names are:

- `1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE`
- `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC`
- `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`

The second has an **existing published formal halting equivalence**, not a
separate new decision: Cryptids'
[`isHalt_HHH1LC_iff_HHH0LA`](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Equivalences.lean)
identifies its halting status with the table differing only at the terminal
instruction `---0LA`, which *is* in this snapshot. This equivalence
predates this inventory.

## How to reproduce and reuse

- All **89** upstream filenames are frozen verbatim in
  [`resources/cryptids-bb6-modules-c86f1586.txt`](../../resources/cryptids-bb6-modules-c86f1586.txt)
  with the exact source commit. They were retrieved from the pinned public
  repository's recursive Git tree.
- [`tools/cryptids_holdout_modules.cjs`](../../tools/cryptids_holdout_modules.cjs)
  reads this manifest and the original 663-root list, generates a deterministic
  machine-by-machine JSON cross-reference, and reports the counts above. The
  tool is CommonJS, uses standard Node file-reading libraries, and writes no files.
- Cross-check any promising root by opening its **original upstream Lean source**.
  Confirm the literal `target` RLE, theorem name, exact semantic/halting
  proposition, pinned build/CI, and axiom audit before asserting a proof status.
  `M_*.lean` source existence by itself certifies *none* of those facts.
- The companion
  [rooted ledger](./README.md) already correctly marks **one** source-confirmed
  externally proved nonhalting root (A6/F287), and otherwise retains
  `not checked` where a machine-level outcome has not been audited. Preserve
  that distinction.

**Evidence limit.** These are source *filenames* matched to rooted transition
strings, not 86 settled holdouts, not a verified mapping of all repository
formalization theorems, and not an exhaustive enumeration certificate.
The source tree itself may contain other certified facts in shared files,
and the 663 entries are a dated historical list rather than today's verified
open frontier. `results/` is intentionally unchanged.

**Research implication.** Before building yet another counter abstraction for
a root in the matched subset, read the pinned upstream proof and the repository's
existing local bridge. On unmatched roots, inspect related source names and
root-preserving conjugacies rather than assuming no outside formalization exists.
The highest-value remaining mathematical work is still a machine-level
root decision and a globally complete enumeration-to-certificate chain.
