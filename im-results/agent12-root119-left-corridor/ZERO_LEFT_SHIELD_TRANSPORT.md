# Zero-left even-run shield transport

**Status:** intermediate formal result; original-source CI is pending. This belongs in `im-results/`, not `results/`.

## Theorem

`Root119ZeroLeftShield.lean` proves the tape-level statement `zeroLeftEvenOutTape_preserves_NoLeft1100`:

For every natural (n), tape (t : \mathbb Z \to \mathrm{Bool}), and head (h), if no four consecutive cells strictly before (h) contain (1100), then the exact output tape of the zero-left even-run macro contains no (1100) strictly before its returned head (h+2n+2).

The predicate `NoLeft1100 t h` is exactly the tape/head form of `NoLeft4 true true false` from `Root119BShield.lean`.

The companion theorem `zeroLeftEvenRun_exact_with_NoLeft1100` composes this transport with the existing exact source-level return law. Under its local corridor hypotheses, the macro returns in exactly (2n+12) primitive transitions to B/0 at (h+2n+2), with the complete output tape specified, and the 1100 exclusion is preserved.

## Proof structure

- The even sweep writes alternating (10) pairs. A four-window starting in the swept interior cannot begin with (11).
- The macro's terminal (11) pair is beyond the last start position for a forbidden word ending strictly before the returned head.
- The fixed prefix cells at (h-3,ldots,h) are (1010) for (n>0); the (n=0) boundary is handled separately.
- The region at or left of (h-4) is unchanged by the existing `zeroLeftEvenOutTape_left` lemma. The only windows crossing the old boundary are ruled out by the fixed prefix values.

The result is for arbitrary exterior tape; it does not assume a blank exterior.

## Verification status and limitation

Lean 4.36.0-rc2 compiled the new proof in a local interface harness that reproduced the exact tape definitions and existing left-exterior lemma. The tape-preservation theorem's axiom report was `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.

The combined theorem was also typechecked in that harness, but its return-law and `shuttleRun` interfaces were axiomatized there. **That is not original-source verification.** The manual workflow `.github/workflows/agent42-root119-zero-left-even-run.yml` has been extended to compile the original return module to an `.olean`, compile this new module against it, reject `sorryAx`, and rerun both existing Node audits. It remains `workflow_dispatch`-only, as previously directed; this invocation has no workflow-dispatch action, so the original-source run still needs to be dispatched.

## Research consequence

Agent42's 10M blank-root replay reported 18 zero-left even-run intervals among the previously unmatched B/0 intervals. Once the manual original-source workflow passes and the replay confirms the full hypotheses and input shield for each instance, these intervals can be upgraded from finite pattern matches to applications of the conditional source theorem, with shielded B/0 endpoints.

This does **not** prove that every reached B/0 section satisfies one of the known macro corridors, does not close the remaining macro-graph induction, and does not decide the auxiliary #119 machine or BB(6).
