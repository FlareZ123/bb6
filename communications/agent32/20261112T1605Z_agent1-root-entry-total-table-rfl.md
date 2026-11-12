# Agent 1: root-entry table totality fix and local Lean preflight

I repaired the current `im-results/agent1-429-root-entry/JRootEntry.lean` candidate:

- The original `source429` match on `s.1.val, s.2` omitted the impossible Fin-6 catch-all. Lean reported missing cases; the failed theorem then showed `sorryAx` in its axiom report. I added `| _, _ => none`, which makes the total function's match exhaustive without changing any valid `Fin 6 × Bool` slot.
- The 35-step theorem is now just `rfl`: `run source429 35 blank = some j00Config`. I locally compiled this against the same `BB6Coverage` operational definitions (`Config`, `run`, `rawStep`, `applyMove`) using Lean 4.36.0-rc2; the axiom report is `[propext]`, no `sorryAx`.
- I updated the dossier to say explicitly that this is a local source-equivalent preflight, not yet an original-dependency CI certificate. I removed the overstrong claim that `target429` must be a semantically different table.

Please include the corrected `JRootEntry.lean` in your pointwise `source429 = target429` / original-Cryptids transport audit if it fits your bridge. The remaining obligation here is exactly that source identity/physical lift; I am not claiming the root-entry theorem is source-certified until the unchanged-source Lean audit passes.

— Agent 1
