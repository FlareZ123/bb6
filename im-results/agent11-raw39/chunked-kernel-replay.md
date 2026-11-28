# Bounded-chunk Lean kernel replay for large accepted proof imports

**Status (28 November 2026):** The algorithm is implemented and two actual
Lean 4.36.0-rc2 source smoke tests passed. Large Raw39 and Raw47 Canonical40
consumers are running; **no global frontier decrement is claimed without
their completed original-source and transitive-axiom audits.** This is
reusable proof-import infrastructure, **not a mathematical Busy Beaver bound**.

## Problem and construction

Independently source-accepted BB(6) proof artifacts often export same-named
Lean `.olean` modules built in different source closures. Importing both sets
naïvely either overwrites a distinct module (unsound) or fails at an import
collision. A prior solution relocates each module in the conflicting import
cone and replays selected proof declarations through Lean's kernel, but can
require thousands of fresh Lean processes, each reimporting a growing base.

The new [chunked kernel replay](chunked_kernel_replay.py) uses the **unchanged
semantic relocation plan** of [stage_relocate.py](../agent32-raw59/kernel-slice/stage_relocate.py)
and the **same Lean kernel checker**
[KernelStage.lean](../agent32-raw59/kernel-slice/KernelStage.lean).
The affected import cone is upward closed: a module importing an affected
module is affected. List the affected modules in original dependency order
and partition this list into consecutive blocks of size at most `b`.
For block `i`, prepare one new module whose imports are the previous
checked block and all unchanged direct source imports of modules in this
block. Then ask `KernelStage` to rename **all root-reachable declarations
in this block** with a common prefix and replay them under those imports.
Only after kernel success is the resulting object exposed to the consumer.
This replaces about `M` costly stage invocations by at most `ceil(M/b)`.

### Why batching preserves soundness

Induct on the ordered blocks. For the first, every external proof reference
lies in an unchanged authenticated import; internally referenced declarations
are within the block. The existing `Lean.Replay` operation checks their
renamed constants together, rejects unsafe, partial and axiom declarations
from the relocated set, and writes the checked object only on success.
For the induction step, dependencies in prior affected blocks are available
through the preceding checked stage, and dependencies outside the affected
cone remain in the base. Topological order excludes references to future
blocks. Repeating the identical kernel-replay check on all declarations of
this block therefore preserves the induction invariant. The consumer must
still compile a *new source theorem*, check table equality and inspect its
**transitive** axiom profile; a staged object alone is not proof acceptance.

The original per-pair import comparator could itself start thousands of
fresh Lean processes. [CompareKernelImportsBatch.lean](CompareKernelImportsBatch.lean)
checks an entire list of original object pairs in **one** Lean process, using
the same kernel-relevant fields: module flag, imports, declared names,
constant infos and extra constant names. The modified generic planner accepts
`comparator_batch` without weakening its existing comparator API. Unknown,
missing, extra or malformed comparison results cause failure; they are never
treated as equivalence.

## Import-compatible fast path

If the original producer root is **not** in the affected import cone,
the old planner raised an error. The new explicit `allow_compatible=True`
path instead preserves the original module names, copies only absent
source-authenticated modules, reuses accepted base objects where exact
kernel data agrees, and **performs no relocated replay**. It checks every
different-byte duplicate's exact kernel data, including import declarations,
and refuses any unresolved collision. The final original-source and axiom
audit still decides acceptance. A dedicated three-way smoke (true collision,
two-batch collision, and no-collision fast path) is the next acceptance gate.

## Actual acceptance and runnable targets

| Source gate | Evidence |
|---|---|
| Two genuinely conflicting `Common.olean` versions plus dependent theorem, **one chunk** | [CI 46125547642](https://github.com/FlareZ123/bb6/actions/runs/46125547642): two new constants replayed by kernel; resulting proof and independent Lean consumer had no axioms |
| The same dependent theorem split across **two sequential chunks** | [CI 46125794862](https://github.com/FlareZ123/bb6/actions/runs/46125794862): stages each replayed one declaration; final imported theorem and consumer had no axioms |
| Batch comparator equality and difference, plus chunk replay | [CI 46127191254](https://github.com/FlareZ123/bb6/actions/runs/46127191254): one-chunk and cross-chunk kernel and batch comparator passed, compatible plan constructed; final CLI failed on absent empty `chunks` key (patched and rerun needed) |
| Accepted complete Raw39 parent imported into original-source Canonical40 | [CI 46125731816](https://github.com/FlareZ123/bb6/actions/runs/46125731816): **pending** |
| Original-source Raw47→Canonical39 via chunked kernel replay | [CI 46126483858](https://github.com/FlareZ123/bb6/actions/runs/46126483858): **pending** |

Usage: import `relocate_chunked` from this directory and call it with the
same authenticated `producer_files, base, work, root_module, root_names,
prefix, tool` as `stage_relocate.relocate`, plus `chunk_size=64` and,
after exact batch-source acceptance, `comparator_batch=HERE /
"CompareKernelImportsBatch.lean"`. It returns `(report,output,names)`;
`report["staged_root"]` is the **last chunk module**, not the original
producer root name. The `report.json` records original collision SHA-256s,
selected source theorem names and each resulting checked chunk SHA-256.
The full Raw39 consumer is
[consume_raw39_kernel_chunked.py](consume_raw39_kernel_chunked.py). The
existing Raw47 consumer has a new opt-in `--transport chunked` mode.

**Limits:** The kernel replay check is decisive for each emitted declaration
but does not resolve semantic mismatches between genuinely different base
definitions, nor does it automatically prove table equivalence in the new
consumer. Memory use rises with the number of declarations inside one block;
reduce `chunk_size` for unusually large declarations. Never count a
prepared artifact, a smoke test or a pending CI run as the final Cover theorem.
