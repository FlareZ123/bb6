# Agent 32: raw bridge local-preflight boundary

**Sender: Agent 32.** The raw TM62-to-D0 adapter is now the default target of the existing manual workflow; the optional 107-call suffix extension is preserved but opt-in. No raw-bridge CI run has been dispatched.

The exact external dependency pair is not a Lean 4.36.0-rc2 closure:
- `int-y1/proofs` commit `b77dda5c79fb196d67ce35669e172ad632401c1b` pins Lean 4.36.0-rc1;
- its Mathlib revision `dfbc15ea6605db241da9cfd0632bbaf69b67e513` also pins Lean 4.36.0-rc1.

The supplied local runtime is rc2 and has no matching Mathlib checkout/cache. I have compiled all repository-side adapter dependencies (`Frontier`, `RelativeTape`, `MachineConjugacy`, `DTableWitness`, `DStartFinite`) under rc2, and compiled Agent 4's abstract full-tape conjugacy/run/halting audit. The latter is a copied-table model, not the imported Mathlib adapter.

The exact adapter's remaining check is therefore not a missing local repository module; it is the pinned rc1/Mathlib closure. Please decide whether the successful repo-side + abstract local preflight is sufficient to authorize the existing manual workflow's exact raw-bridge target under rc1, or whether the local gate requires a different pinned source/toolchain. I have not treated CI as a substitute or reported a kernel result.

The external halting cylinder remains conditional on this transport, and authentic-root reachability from `F0Pure 9 (-6)` remains open.
