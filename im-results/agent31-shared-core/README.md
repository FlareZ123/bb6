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


## Canonical73 source-audit path (2026-11-25)

The canonical74/73 draft now has a real consumer path in `.github/workflows/agent47-raw114-graft.yml`:

- Dispatch with `target=canonical73` and `canonical76_run_id=<run containing raw107-canonical-shared-core>`.
- The workflow downloads only the canonical77 + raw107 shared-core artifact, then regenerates Raw112, Raw117 and Raw110 source data and compiles `Canonical73Raw110Composition.lean` plus its complete dependency closure against that one core.
- The job checks the exact 73-entry roster, raw112/raw110 parent membership, mixed-bound soundness, theorem axiom profiles (allowing only `propext`, `Classical.choice`, `Quot.sound`), and records source/compiler/object-manifest hashes.
- It does not depend on the separate raw112 shard artifacts and does not rerun the expensive canonical76 base build. All 73 retained Covers remain explicit premises, so even a passing run is a conditional roster theorem, not an exact BB(6) result.

Run `45653927442` is the first consumer attempt. It uses the early `raw107-canonical-shared-core` artifact from run `45632293194` (artifact `15033523473`, 190,965,153 bytes). Run 456322 failed later in its canonical76 consumer step, but the shared-core artifact had already been uploaded. At 16:27 UTC run 45653927442 was reconstructing Raw112/Raw117/Raw110 source data; no source-acceptance claim is made until its final Lean and axiom audit succeeds.

The raw112 full parent audit run `45646559852` failed on runner shutdowns (exit 143) in several shards, without Lean theorem diagnostics. The canonical73 consumer deliberately regenerates and recompiles Raw112 from committed sources against the canonical shared core rather than reusing those failed shard artifacts. Raw110 parent source is restored from artifact run `45593652030`.
