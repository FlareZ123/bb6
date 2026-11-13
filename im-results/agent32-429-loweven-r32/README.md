# #429 low-even r=32: source-level no-fatal continuation

**Status: intermediate Lean proof candidate; original-source CI pending.** This is one concrete prepared-J instance of the conjectural low-even (r=4k) row. It is not a parameter-uniform return theorem and does not decide the authentic blank-root machine.

## Exact candidate

The source zipper starts at

`junc 45 0 58`

and the predicted 4407-step endpoint is

`junc 11 0 146`.

Here (r=2u-w=90-58=32=4\cdot 8). Substituting (u=45,k=8) into Agent 18's experimental low-even formula gives

- time (4u^2+(22-16k)u+16k^2-26k+261=4407);
- target ((11,4u-4k-2)=(11,146));
- head displacement (9-2u=-81).

The general (r=4k) formula remains conjectural outside separately source-proved instances. This module formalizes only the (u=45,k=8) instance.

## Proof structure

`LowEvenR32NoFatal.lean` separates the exact source path into three finite segments:

| Segment | Steps | Source endpoint | Head displacement |
|---|---:|---|---:|
| Positive-u Junc iteration | 3192 | `midApos 17 54 4` | +56 |
| Intermediate return | 346 | `junc 16 58 0` | -114 |
| Final return | 869 | `junc 11 0 146` | -23 |
| **Total** | **4407** | **`junc 11 0 146`** | **-81** |

The first segment is an instance of the existing inductive `juncPos_iter_mid_delta` theorem. The remaining displacement equations are finite source computations. The three guarded equations compose using Agent 48's `BB429NoFatalGuard.runNoFatal_compose`.

The guard excludes exactly C/0 with a marked immediate right neighbor, the original-machine fatal C/01 gateway. It deliberately permits harmless C/0/blank-right visits. The physical theorem uses `BB429PhysicalBridge.Represents` and `source_run_rep`/ `source_runWithDelta_rep` to lift the endpoint and every prefix to the unchanged complete bi-infinite tape; no finite-window approximation is used.

The final 869-step suffix has the formally recorded C/0 event trace:

| Absolute time from Junc(45,58) | Head displacement | Right neighbor |
|---:|---:|---|
| 3664 | +64 | blank |
| 4069 | +67 | blank |

An independent full source-table replay observed no earlier C/0 events and these two events only. That event-count statement outside the final suffix is simulation evidence, not a separate theorem. The all-prefix no-fatal theorem does not depend on the event census.

## Root connection and limits

Agent 1 derived a 2562-step ordinary-Junc path from `junc 0 0 136` to this `junc 45 0 58` start. Its seven segments use existing ordinary Junc return theorems, but the complete composition and physical frontier theorem were still pending when this module was written. The conditional `blank_root_lowEvenR32_no_fatal` theorem is ready to compose once that genuine-root entry is certified.

The empirical head maximum for this 4407-step segment is +68 relative to its start; it is **not** claimed as a theorem here. The present formal result, once CI confirms it, establishes the exact prepared-source endpoint and excludes the actual C/01 halt gateway at every prefix of this segment. It does not prove that the blank root reaches the segment, does not establish all-time nonhalting, and supplies no BB(6) value or universal upper bound.

Keep this dossier in `im-results/` until a stronger mathematical result is established.
