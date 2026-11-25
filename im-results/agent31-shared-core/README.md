# Agent 31 shared-core roster and suffix-frame work

This directory contains **intermediate, champion-independent proof interfaces**. None of the roster modules here is an exact BB(6) result: every `exact_at_target` theorem leaves all retained `Cover` premises and an attaining blank-start witness explicit.

## Roster layers

- `CanonicalTwoParentRosterOnly.lean`: rebuilds the raw107+raw114 bounds and the 76-entry quotient dichotomy without importing the champion-specific `Canonical77ExactComposition` or `TM63RawUpperInterface`.
- `Canonical75RosterOnly.lean`: applies the source-accepted raw117 cut to the 76-entry roster. Its intended interface is 75 residual Covers at any target B≥7014, plus an attaining witness.
- `Canonical75Raw112RosterOnly.lean`: alternative 75-entry roster obtained by removing the raw112 parent, with target B≥100000.
- `Canonical74Raw107Raw114Raw117Raw112RosterOnly.lean`: combines the raw117 and raw112 cuts. Its `decide` proofs test that the raw112 parent remains distinct after the raw117 cut and that exactly 74 representatives remain. This is a draft until source-compiled.

The 75/74 counts and raw112 membership are intentionally executable Lean checks, not assumptions. If a count or membership proof fails, inspect the actual quotient representative rather than weakening the theorem.

## Right-suffix frame lemma

`../agent31-three-hole-tnf/RightFrame.lean` adds `SafeRight` and `run0_append_right_of_safe_eq`. It proves that a finite run on an explicit right-tape prefix extends unchanged under every opaque appended suffix, provided every rightward move consumes a cell from the visible prefix. This is intended for recursive counter encodings such as the raw112 high stack.

The frame theorem and its exact-output corollary were tested locally with Lean 4.36.0-rc2 and then compiled in the repository import closure by CI run 45597008330. The raw112 leaves no longer depend on the earlier high-counter-grammar route: the current proof path is a 7-state carry extension with a counted-sweep growth invariant, plus a 4-step/2-step stuttering simulation for the sibling leaf. RightFrame remains a generic reusable lemma, not a dependency of those raw112 proofs.

## Current evidence status (2026-11-25)

- Raw112 original-semantics carry/sibling audit: run 45595822219 passed; the two `never` theorems reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Raw112 full parent-cover audit: run 45596113340 was in progress at last check. Its intended theorem is a `Cover (WeightedBound 100000)` for the raw112 parent.
- Right-suffix frame plus sibling audit: run 45597008330 passed; artifact 15014545618 was uploaded.
- Shared canonical raw107/raw114/ champion audit: run 45591337117 was still compiling its shared closure at last check.

Do not treat the pending runs or draft roster modules as source-accepted until their CI artifacts and theorem axiom profiles are available.


## Canonical73 / canonical72 source-audit path (2026-11-25)

The `target=canonical73` path in `.github/workflows/agent47-raw114-graft.yml` now compiles two related conditional roster theorems against one canonical77 + raw107 shared core:

1. `Canonical73Raw110Composition.lean`: raw107 + raw114 + raw117 + raw112 + raw110 parent cuts, leaving 73 quotient representatives.
2. `Canonical72Raw121Graft.lean` (Agent38): proves the Raw121 parent remains in that 73-entry roster, removes it with `graftRoster`, and obtains a 72-entry roster. Its local parent bound is 4063, lifted to the common 6,766,859 bound.

The job regenerates Raw112, Raw117, Raw110 and Raw121 data from committed sources; restores the Raw110-specific parent source artifact from run `45593652030`; compiles both roots in one Lean closure; and audits the Raw112/Raw110, canonical75/74/73, Raw121 and canonical72 theorem axiom profiles. It explicitly selects the canonical shared `ThreeHoleAudit` and `TNFPilot` modules to avoid duplicate-source collisions. On success it uploads both `canonical73-raw110-raw112-roster-only-certified` and `canonical72-raw121-raw110-raw112-roster-only-certified`.

**Status: not source-accepted yet.** Run `45653927442` failed before Lean elaboration because the Raw110 artifact restore created an ambiguous `ThreeHoleAudit` source. Run `45654703987` also failed before Lean elaboration because the restored artifact duplicated `TNFPilot`. These were source-index collisions, not theorem failures. Agent38 fixed the restore/override path in commit `5a3fdbe33ae7ffccfe17ecb1833bec1264244f2f`; the current workflow includes both explicit overrides and excludes the duplicate TNFPilot copy.

The current source-audit run is `45655459117`, dispatched by Agent38 with `target=canonical73` and `canonical76_run_id=45632293194`. Agent38 verified that run 456322's `raw107-canonical-shared-core` artifact (artifact `15033523473`) is valid and was uploaded before the stale canonical72 consumer failed; the new run uses that artifact. The separate build `45647053824` continues independently but is not required for this attempt. Run 456554 uses workflow head `bddeb6841ca3c13e9fdfad786d1ef4ebf588c4e3`, including the Raw121 72-entry extension and both explicit source-index fixes.

The separate Raw112 shard audit run `45646559852` failed with runner shutdowns (exit 143), without Lean theorem diagnostics. The canonical73 job regenerates and recompiles Raw112 from committed sources against the canonical shared core rather than reusing those failed shard artifacts.

Even if both new roots pass, the result remains conditional: all 73 Covers for the first roster, or all 72 Covers for the Raw121-grafted roster, and an attaining champion witness remain explicit premises. This is not an exact BB(6) result.
