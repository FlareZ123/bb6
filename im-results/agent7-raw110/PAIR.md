# Raw110 final-pair reduction

The two one-hole residuals 5/161 and 5/790 differ only at F1:

- fast: `1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC0LF`
- slow: `1RB---_1RC0RA_0RD0LF_1LD1RE_0RB0LC_1LC1RD`

Whenever the fast machine is in F it has just written zero immediately to the right of its head (both incoming rows C1 and F1 write zero and move left). In such a configuration F1 in the slow machine executes F1→D0→D1→E1→C1, returning to F with exactly the tape and head of the single fast F1 step. All other rows are identical. The only missing row A1 is common. Hence both infinite partial blank runs are equivalent: every fast step expands to one or five slow steps, and any finite fast failure expands to a slow failure. One nonhalting proof therefore suffices for this pair, provided the source completion bridge is established.

The theorem `forever_iff` in `Raw110PairMacro.lean` was locally compiled in Lean 4.36.0-rc2 against a minimal model with exact copied definitions of Move, Z0, move0, step0, run0, run0_add and join0. Axiom output: five [propext]; simulate_prefix and forever_iff [propext, Quot.sound]. The committed source imports the actual SweepPumping module; source closure acceptance and transfer to universal compatible completion NeverHalts are separate outstanding checks. No claim that either machine is nonhalting, nor an unconditional raw110 closure.

The new `Raw110PairBridge.lean` implements both directions between infinite sparse runs and universal `NeverHalts` of compatible completions: fill all holes with a genuine halt to establish the reverse direction, and use `zrun_sound` for the forward direction. Its theorem `universal_never_iff` compiled locally against exact relevant source definitions and proofs from Frontier, RootShift, SparseZipper, and SweepPumping; kernel axioms [propext, Quot.sound]. Committed original-module import still needs CI source check. It accepts either member's certificate and transfers to the other without searching or simulating again.
