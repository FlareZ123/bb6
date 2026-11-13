# #429 low-even r=32: source-level no-fatal continuation

**Status: concrete leaf module compiled against the original-source dependency chain; a blank-root composition candidate has now been added, and integrated manual validation remains pending.** Run [43365025686](https://github.com/FlareZ123/bb6/actions/runs/43365025686) compiled this complete module and printed axiom reports for every public declaration: only standard `propext`, `Quot.sound`, and `Classical.choice` dependencies, with no `sorryAx` in this module. The overall workflow failed later in unrelated `Low43Continuation.lean`, whose declarations did contain `sorryAx`; it was not a green workflow. The isolated manual-only gate is `.github/workflows/agent32-loweven-r32.yml`. This is one concrete prepared-J instance of the conjectural low-even (r=4k) row, not a parameter-uniform return theorem and not a decision of the authentic blank-root machine.

## Exact candidate

The source zipper starts at

`junc 45 0 58`

and the predicted 4407-step endpoint is

`junc 11 0 146`.

Here (r=2u-w=90-58=32=4\cdot 8). Substituting (u=45,k=8) into Agent 18's experimental low-even formula gives

- time (4u^2+(22-16k)u+16k^2-26k+261=4407);
- target ((11,4u-4k-2)=(11,146));
- head displacement (9-2u=-81).

The general (r=4k) formula remains a separate unverified candidate in PR [#82](https://github.com/FlareZ123/bb6/pull/82). This module formalizes only the (u=45,k=8) instance.

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

## Blank-root composition candidate

Agent 1's `RootJunc136To45.blank_root_no_fatal_to_junc45` composes the genuine blank-root prefix through Junc(0,0,136) with seven ordinary Junc transitions. It states a full-tape physical path from blank to `Junc(45,0,58)` at step 16,280, with C/01 excluded at every prefix.

New `LowEvenR32RootChain.lean` composes that theorem with this module's 4,407-step physical no-fatal leaf. Its theorem `BB429LowEvenR32RootChain.blank_root_lowEvenR32_to_junc11_146` states that the authentic blank root reaches `Junc(11,0,146)` at step 20,687 and excludes C/01 at every primitive prefix through that endpoint. It also preserves the ordinary-bridge frontier bound and the -81 head displacement of the final leaf.

**This composition is a proof candidate, not yet a CI-certified theorem.** Agent 6's manual-only `.github/workflows/agent6-429-low42.yml` already compiles the root bridge and its dependencies; the remaining integration is to compile `LowEvenR32NoFatal.lean` and `LowEvenR32RootChain.lean` in that same unchanged-original-source run and audit their axiom reports. The isolated r=32 leaf workflow remains useful independently.

## Root connection and limits

Agent 1 is handling the separate 2562-step ordinary-Junc path from `junc 0 0 136` to this `junc 45 0 58` start. Its seven segments use existing ordinary Junc return theorems, but the complete composition and physical frontier theorem remain uncomposed and unverified. The conditional `blank_root_lowEvenR32_no_fatal` theorem is ready to compose once that genuine-root entry is certified.

The empirical head maximum for this 4407-step segment is +68 relative to its start; it is **not** claimed as a theorem here. The module-level compile establishes that the Lean declarations for the exact prepared-source endpoint and every-prefix C/01 exclusion elaborate against the source dependency chain without `sorryAx` in the module. The isolated manual gate remains the next validation checkpoint. It does not prove that the blank root reaches the segment, does not establish all-time nonhalting, and supplies no BB(6) value or universal upper bound.

Keep this dossier in `im-results/` until a stronger mathematical result is established.
