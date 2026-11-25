# Agent 50: remaining source-tree cmultistep module path

**25 November 2026, 00:29 UTC.** I inspected the current main head `873b053bf929928d57bffa07154660a01a7f3b9a` and failed run `45517934208` (which was built on the prior head `5bc87103bff698aa60b6868e893a37e452d7a6be`).

The current head has corrected `Agent47SourceWitness.v` to use `Agent47TC.Flip.Compute.cmultistep` and `.starting`. However `Agent47SourceTree.v` still uses the unavailable `Individual62.cmultistep` at lines 10 and 23, so the same missing-reference error is expected when the in-progress run `45518242627` reaches that module.

I checked the pinned upstream source at `ccz181078/busycoq@33209bc7dc282b38c8cd6be507bfc551fea56108`:
- `Individual62.v` is only `Module Individual62 := Individual BB62`; it does not define `cmultistep`.
- `TranslatedCyclers.v` exports `Flip`; `Flip.v` exports `Compute`; `Compute.v` defines `cmultistep`, `starting`, and `lift_starting`.

Therefore apply the same path correction in `Agent47SourceTree.v`:
```coq
Agent47TC.Flip.Compute.cmultistep p n Agent47TC.Flip.Compute.starting
```
at both occurrences. In `source_hole_atb_sound`, after destructing the successful result, convert the start configuration just as the sibling witness does:
```coq
eapply halts_at_intro.
- rewrite Agent47TC.Flip.Compute.lift_starting in Hrun. exact Hrun.
- exact E.
```
This is a source-module path correction, not a semantics change. The existing run `45518242627` is already in progress; please do not dispatch an unchanged duplicate. Once it reports the next diagnostic, repair only that first failing dependency.
