# Five-slot leaf preflight: verified helper, full closure still pending

Checkpoint: 2026-11-20T03:52:28.278Z

## Scope and pinned source

Current main head inspected: `bcce600a41fd89f0c6dc3c32d9a0f8b5d1d8fc31` (2026-11-20T03:50:08Z). The following relevant blobs are unchanged at that head:

- `FiveSlotLeafGraft.lean`: `757290d18b1990457a6a6ae4fa1b4d6641fbe202`
- `IncrementalAudit.lean`: `3e91e42c90f6380bbecc4a83489bf68962ab995c`
- `LassoTraceAudit.lean`: `c0922233376b30ed67e247b88d253eafd60cc852`
- `TranslatedFiveSlot.lean`: `7ed9614c5bba925121d1fbdf11ecf54dfbd34615`
- `TranslatedFiniteOracle.lean`: `7e2acfaa9fcfbb7c20a7187108efa093e206a0e5`
- `TranslatedCycle.lean`: `a7abe8da947d22f7c4086b441c164e411eb9e2be`
- `RootShift.lean`: `80b56fb040f7db81277fcf52cd43e6127fe365ba`
- `Frontier.lean`: `115438c4f244b5416a91be4dd7a3f12103d5448d`
- `FrontierAudit.lean`: `693cd1896794d03cfce84d7b3a54fdab73d03709`
- `FrontierMass.lean`: `3fc03cc81a91a96fbee256835493339d3b3e5474`

## Local Lean check actually completed

The provided split archive was reconstructed and Lean 4.36.0-rc2 installed locally (`b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`).

I reconstructed the `Frontier`, `FrontierAudit`, and `FrontierMass` imports from the GitHub source text and compiled them, then compiled the current `IncrementalAudit.lean`. The local `IncrementalAudit.lean` passed `git hash-object` with the exact upstream blob SHA `3e91e42c90f6380bbecc4a83489bf68962ab995c`. The three reconstructed dependency files did **not** pass byte-for-byte blob comparison, so this is a local module-level proof check against manually reconstructed imports, **not** an exact-source dependency-closure preflight.

Commands (after setting `PATH` to the extracted Lean bin directory and `LEAN_PATH=/tmp/bb6-preflight`):

```sh
lean -o Frontier.olean Frontier.lean
lean -o FrontierAudit.olean FrontierAudit.lean
lean -o FrontierMass.olean FrontierMass.lean
lean -o IncrementalAudit.olean IncrementalAudit.lean
lean Check.lean
```

The exact `IncrementalAudit.lean` source compiled. A separate `Check.lean` confirmed:

- `BB6Coverage.graftCertificate_open_iff`: axioms `[propext, Quot.sound]`
- `BB6Coverage.addCertificate_open_iff`: axioms `[propext, Quot.sound]`
- `BB6Coverage.addCertificate_closes_source`: axioms `[propext, Quot.sound]`

No `sorryAx` appeared in these profiles. This closes the previously uncompiled helper-level open-set theorem at the exact module source level, but does **not** satisfy the full current-main closure requirement. The helper-only compile is not acceptance of the graft.

## Static mathematical reading of the five-slot candidate

The current `TranslatedFiveSlot.lean` fixes five entries:

- A/0 = 1RB
- B/0 = 1LC
- C/1 = 0RD
- D/1 = 1RE
- E/0 = 1LC

The blank-root run reaches C at head 0 after two steps, with marked cells `{0,1}`. The three-step macro C/1, D/1, E/0 returns to C at head +1 and translates that finite support to `{1,2}`. The source uses `finiteTranslatedCheck agent27WordPump 2 3` and `finiteTranslatedCheck_sound` to obtain a nonhalting cylinder for every compatible completion. This is a genuine translated finite-support cycle, not a right-tail word-pump argument.

The four-slot parent P4 has mass `25^8`; adding E/0 gives a five-slot child of mass `25^7`. Thus the child is one twenty-fifth of the P4 parent and `1/25^5 = 1/9,765,625` of all `25^12` six-state/two-symbol tables. The integration target's intended contract is:

- every completion of P4 was open in the prior depth-four physical audit;
- the new five-slot source cylinder is nonhalting;
- `addCertificate_open_iff` makes the graft's new open set exactly the old open set minus that source cylinder;
- exhaustive coverage and total mass conservation remain intact.

This is source inspection only: `FiveSlotLeafGraft.lean`, `LassoTraceAudit.lean`, `TranslatedFiveSlot.lean`, and their full transitive imports were **not** compiled locally. Do not report the five-slot graft as accepted until the exact current-main closure compiles and its requested axiom profiles are checked.

## Remaining blocker and next action

The shell now has a working Lean runtime, but there is still no local repository checkout. `git clone` and direct `curl` fail because DNS/outbound networking is unavailable. GitHub connector reads do not materialize a checkout into this shell.

Obtain a checkout or exact source bundle accessible to the local runtime, then compile the full pinned closure (including `LassoTraceAudit`, `RootShift`, `TranslatedCycle`, `TranslatedFiniteOracle`, `FrontierExtract`, `FrontierUnique`, `FrontierManifestMass`, `ResidualFrontierManifest`, `IncrementalAudit`, and `FiveSlotLeafGraft`) and inspect the exported axiom profiles. Do not dispatch CI as a substitute for this local preflight. Keep this in `im-results/`; it is not a publishable BB(6) result and does not change the fact that BB(6) remains unresolved.


## Existing workflow's exact build boundary

The existing workflow `.github/workflows/agent32-zero-path-global.yml` (blob `ab46cd0260187a1516182ddb80eb0f77aec6e392`) already defines the isolated manual target `verify_five_slot_leaf_graft`. Its shared source-proof step compiles the base modules in this order:

1. `Frontier`;
2. `RayClosed`, `RayChecker`, `RayEntry`, `RayFinite`, `RayTurnExample`, `RayFiniteOracle`, `FiniteHalting`;
3. `Symmetry`, `RayMacro`, `EntryMacroOracle`, `EntryMacroLeft`;
4. `DirectedDrift`, `ZeroMaskOracle`, `FiniteDecision`;
5. `FrontierAudit`, `FrontierMass`, `ZeroPathAudit`, `ControlPathAudit`, `ZeroRowAudit`, `PhysicalTraceAudit`, `FiniteLassoOracle`, `LassoTraceAudit`, then `ReadOneLeaf`.

The five-slot-specific step then compiles, in order, `RootShift`, `TranslatedCycle`, `TranslatedFiniteOracle`, `IncrementalAudit`, `TranslatedFiveSlot`, and finally `FiveSlotLeafGraft`, teeing the target's output and rejecting `sorryAx`. This is the authoritative isolated target sequence once an exact local checkout is available.

The separate `export_frontier` step compiles `FrontierExtract`, `FrontierUnique`, `FrontierManifestMass`, and `ResidualFrontierManifest`. These are not imports of `FiveSlotLeafGraft`; the target comment and source definitions were checked directly and both `agent27Depth4Audit` and `depth4ResidualAudit` are exactly `lassoPhysicalTraceAudit emptyTable 6 6 12 12 2 4 4`. Agent 12's requested manifest comparison is therefore a separate reporting-path audit, not a direct dependency of the isolated graft theorem.
