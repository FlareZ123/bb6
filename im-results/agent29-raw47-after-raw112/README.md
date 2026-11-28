# Raw47 after Raw112: accepted-lineage 38-to-37 consumer

## Exact question and current proof boundary

The original-source Lean 4.36.0-rc2 run [46150267242](https://github.com/FlareZ123/bb6/actions/runs/46150267242) accepts
`BB6.Agent10Raw112Canonical38AfterRaw39.exact_at_champion_score`
with **38 residual `Cover` premises**, after consuming the source-accepted
Raw39 and Raw112 complete parents. This is a different valid ordering from
the active direct Raw39+Raw47 route. It is not BB(6) maximality.

The remaining Raw47 parent is the five-transition seven-hole table
`1RB---_1RC---_0RD---_1LD0RC_------_------`.
Its separate complete original-source parent Cover at every weighted
`B ≥ 143977` passed [46068688341](https://github.com/FlareZ123/bb6/actions/runs/46068688341).
The unconsumed proof edge is a *common-kernel-environment* transport of that
Cover into the newly accepted Raw112-after-Raw39 lineage, followed by exact
roster membership and sound removal.

The source `Raw47Canonical37ConditionalAfterRaw112.lean` states and proves
in this exact roster, subject to acceptance of the source-checking job:

- Raw47 occurs **once** among the 38 retained quotient representatives;
- removing its literal source table gives **37** representatives, none matching Raw47;
- supplying `Cover (WeightedBound 6766859) p47` gives a sound 37-member
  conditional global reduction and the fixed-score `ExactBB6` theorem.

The separately accepted Raw47 local theorem already has sufficient numerical
strength; the conditional Cover premise is *not* a new mathematical
uncertainty. It must nevertheless be discharged by authenticated transport
and source/axiom auditing. **Neither a 37-quotient bound nor unconditional
global maximality is claimed until that final integration succeeds.**

## Reproduction and acceptance

`check.py` compiles the original-source conditional module in the *same
Lean environment* built by the accepted Raw39+Raw112 consumer, checks exact
theorem profiles and preserves a deterministic receipt. It uses the existing
manual `.github/workflows/agent10-raw112-after-raw39.yml` with
`raw47_conditional=true`; first source run [46152224484](https://github.com/FlareZ123/bb6/actions/runs/46152224484)
was queued as of preparation, **not yet accepted**.

`full.py` is the stronger integration attempt: after a successful conditional
source check it reclaims the redundant downloaded Raw112 source staging,
imports hash-authenticated Raw47 producer proof objects, replays the
import-affected cone with the existing trust-level-zero kernel relocator, and
compiles `Raw47Canonical37AfterRaw112.lean`. The latter proves literal
identity of the two parent functions by definitional equality, imports the
accepted `Raw47KernelBridge.cover_at`, and eliminates the Raw47 Cover premise,
leaving exactly the other 37 Cover hypotheses. The manual workflow exposes
`raw47_full=true` for this route. **This full integration is staged but
not yet source accepted.**

The source acceptance gate requires compilation against the actual accepted
dependencies, transitive axioms within `{propext, Classical.choice, Quot.sound}`,
and no `sorryAx` or oracle. CI infrastructure failures or compilation errors
must be reported distinctly. The accepted Raw112 parent artifact is
[15263639929](https://github.com/FlareZ123/bb6/actions/runs/46146501930/artifacts/15263639929);
the accepted Canonical38 receipt is
[15265958695](https://github.com/FlareZ123/bb6/actions/runs/46150267242/artifacts/15265958695).

Independent read-only preflight of
`im-results/agent50-raw47-canonical41/canonical40-raw-index-audit.json`
found Raw39, Raw112 and Raw47 each exactly once among Canonical40's 40 IDs,
and a 40→38→37 set difference for that ordering. This is **manifest
reconstruction**, not a substitute for the source Lean membership proof.

## Remaining obligation

Once a source-accepted 37-representative consumer exists, every one of the
37 residual `Cover` assumptions is still unproved at the global champion
score unless independently discharged. Keep this dossier conditional until
the original-source run and exact parent transport pass. Do not extrapolate
a whole-machine nonhalting or an exact BB(6) value from the quotient count.

## 2026-11-28 checkpoint recovery

The conditional 38-to-37 source theorem is already accepted in the Raw112-first
Canonical38 environment. Two full-consumer attempts, [46155256842](https://github.com/FlareZ123/bb6/actions/runs/46155256842)
and [46156390048](https://github.com/FlareZ123/bb6/actions/runs/46156390048),
both reached the trust-level-zero Raw47 replay and passed respectively 31 and
28 `A50Raw47SliceChunk` stages. Both were cancelled before the final
bridge/consumer theorem. Their uploaded artifacts contain evidence and logs but
**not** the `raw47-kernel-replay/objects` directory, so neither is resumable.
These are interrupted computations, not failed mathematical checks; they do
not establish Canonical37.

The existing manual
`.github/workflows/agent10-raw112-after-raw39.yml` now supports a durable
checkpoint protocol:

1. Dispatch with `raw47_full=true`, the accepted Raw112 run `46146501930`,
   and the accepted Raw39 1LE run `46114235329`. Leave `resume_run_id` empty
   for a fresh replay.
2. On every job exit (including cancellation), artifact
   `raw47-after-raw112-checkpoint` stores `report.json` and only the checked
   `objects/A50Raw47SliceChunk*.olean` stage files (not unrelated producer objects).
3. If the run is interrupted, dispatch the same workflow with
   `resume_run_id` set to that prior run ID. `full.py --resume-from` delegates
   to `relocate_chunked`, which reconstructs the import plan and verifies each
   prior stage's source-module list and SHA-256 before reusing it. A mismatch
   fails closed; it never trusts an unverified checkpoint.
4. A successful final run must still compile the original-source
   `Raw47Canonical37AfterRaw112.lean`, export the fixed-score theorem, and
   pass the complete transitive axiom gate. Only then may the public boundary
   move from 38 to 37.

The timeout was raised to 240 minutes so a single uninterrupted attempt can
finish the measured ~39-stage replay. The checkpoint is retained as a recovery
path, not as a weaker acceptance criterion. No new theorem or roster decrement
is claimed by this infrastructure change.
