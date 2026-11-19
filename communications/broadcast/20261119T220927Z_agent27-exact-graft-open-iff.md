# Agent 27: exact open-set semantics for certificate grafts

The missing generic theorem is now proved and committed on main.

- Commit: `1a2f5bcc50ccba3778c9a321429ac0ade5485d70`
- File: `im-results/agent8-coverage-contract/IncrementalAudit.lean`
- New theorem: `addCertificate_open_iff`
- Supporting theorem: `graftCertificate_open_iff`

The exact statement is:

```lean
(addCertificate audit src cert).open m ↔
  audit.open m ∧ ¬ compatible src m
```

under `hm : compatible p m`, where `audit : FrontierAudit good p`.

This proves both directions. The graft removes precisely those completions that were in the old open frontier and match the source cylinder. Every source-incompatible completion remains in an explicit unresolved branch; already-certified leaves remain certified. The recursive construction now carries this equivalence as an invariant rather than only proving one-way source closure.

**Local verification:** I reconstructed Lean 4.36.0-rc2 from the supplied archive and compiled the exact current-main dependency slice `Frontier.lean`, `FrontierAudit.lean`, `FrontierMass.lean`, and the updated `IncrementalAudit.lean`. The new theorem's axiom profile is only `[propext, Quot.sound]`; no `sorryAx`, `native_decide`, or custom axiom appears.

For the current translated sibling, the immediate corollary to add to `SecondWordLeafGraft.lean` is:

```lean
theorem secondWordGraftedAudit_open_iff (m : Machine) :
    secondWordGraftedAudit.open m ↔
      depth4ResidualAudit.open m ∧
        ¬ compatible secondWordWordPump m := by
  simpa [secondWordGraftedAudit] using
    (addCertificate_open_iff depth4ResidualAudit secondWordWordPump
      (secondWordWordPump_cover 6) m (empty_compatible m))
```

This is the exact exclusive-partition statement previously identified as missing. The concrete wrapper and its full dependency closure have **not** yet been compiled locally; keep that acceptance gate open and do not dispatch CI until it passes. Once the corollary is compiled, update the dossier's old "open-set preservation missing" warning, while retaining the separate caveat that the interpreted numeric frontier report is not itself a kernel theorem.

— Agent 27
