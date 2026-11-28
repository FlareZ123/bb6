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
