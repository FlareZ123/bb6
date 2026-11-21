# Agent 32 review: concrete type/import blockers in Cryptids608NonHalt

I reviewed current-main `im-results/agent42-cryptids-current-main/Cryptids608NonHalt.lean` (blob `6a1bc47f71ba6e1affe2ec9949e87189d58dbfaa`) against the exact upstream source at Cryptids commit `3647718b5df22e1a61462dec0376bd204526285a`.

There are two deterministic source-level blockers before any deeper proof review:

1. The file imports `CryptidsTapeAdapter`, `IncrementalAudit`, `ResidualFrontierManifest`, and the six machine modules, but it does **not** import `CryptidsF287`. `CryptidsTapeAdapter.lean` defines `reachable_live_implies_never`, not `not_halts_to_agent8`. The only current declaration of `not_halts_to_agent8` is in `im-results/agent4-coverage-smoke/CryptidsF287.lean`. The six uses are at lines 58, 104, 150, 196, 242, and 288. Therefore the identifier is unavailable in this import closure.

2. Each imported upstream `is_not_halt` has type `BusyBeaver.IsNotHalt target`, not `¬ ConjectureMachines.Halts source_rN`. I checked all six declarations at the pinned upstream commit; they all end with `theorem is_not_halt : IsNotHalt target` (the first five are direct aliases or wrappers; r3 rewrites `target_eq`). The exact bridge theorem is `ConjectureMachines.isNotHalt_toBB_iff_not_halts` in upstream `BusyBeaver/Bridge.lean` line 262:
`BusyBeaver.IsNotHalt M.toBB ↔ ¬ ConjectureMachines.Halts M`.

For each root, the transfer needs an explicit conversion, e.g.
```lean
theorem original_r1_never : NeverHalts original_r1 := by
  apply not_halts_to_agent8 source_r1
  exact (ConjectureMachines.isNotHalt_toBB_iff_not_halts source_r1).mp
    BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.is_not_halt
```
Repeat with the corresponding `source_rN` and module theorem. To resolve blocker 1 cleanly, move the generic `not_halts_to_agent8` declaration from `CryptidsF287.lean` into `CryptidsTapeAdapter.lean` (or a small shared bridge module) rather than importing the F287-specific module into this six-root graft.

This is static type/import review only; I have not claimed a compile or checked the six `oldOpen` computations. These two issues should be fixed before spending compatible-toolchain preflight time.

— Agent 32
