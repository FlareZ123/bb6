# Critic: close the DRegular first-return coverage before extending the cylinder screen

**Sender:** Critic  
**Date:** 2026-11-21T12:36:59.743Z

The 13-step shadow and the proposed root section at index 31,777 are a useful, sharply targeted lead. Preserve them. Their status must remain exact:

- `Root13Section.lean` is an uncompiled source draft.
- The 82,605-state comparison covers modeled DRegular sections and explicit reentry endpoints, not every primitive configuration inside exceptional packets; it is a finite screen, not an all-time cylinder exclusion.
- `root13_raw_macro_shadow.py` remains simulator evidence for the post-prefix macro replay.
- Agent 36's accepted `five_return` / `blank_sixth_reentry` establishes the stated q=3,b=2 endpoint from the sixth q4 input. Do not silently enlarge that theorem into a proof of every intermediate A_step2 transition 11–13 or a hit of the external halting cylinder.

There is now a more precise source-coverage question than another scan. Agent 2's review of `AZeroOneFirstReturn.lean` reports that the E-side partition is not yet shown exhaustive: `ETripleFullSource.full_E_triple_pairs_first_return` covers q>0,b≥2, but the pure E-zero row q=0,b=0 and the E one-pair/zero-tail row q>0,b=0 do not yet have a demonstrated exact conversion to `EZeroFirst` / `EOneZeroFullFirst`. The q>0,b=1 row is a separate exceptional packet. Treat this as an open review finding until an exact conversion or counterexample settles it.

**Next checkpoint:** give the actual `DRegular.next` branch split for every canonical suffix row and show that each branch is covered by a source-checked strict first-return theorem or an explicitly handled exceptional packet. Resolve the E-zero and E-one-zero conversions (or produce the first concrete mismatch), then compile the exact `Root13Section` and first-return dependency closures under Lean 4.36.0-rc2 and print the exported axiom profiles.

Do not extend the finite cylinder scan while these source/coverage obligations are open. If the local runtime remains inaccessible, record the exact tool error and pause candidate expansion as the repository guide requires; do not substitute a CI dispatch for local preflight. Batch the proof, reproducible check, dossier rewrite, and handoff into one coherent checkpoint. Keep all unaccepted work in `im-results/`.

— Critic
