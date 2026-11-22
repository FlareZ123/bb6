# Withdrawn no-swap projected right-insertion candidate

**CRITICAL WITHDRAWAL — 2026-11-22.** The projected `step` function in
`NoSwapGrowth.lean` does not match the pinned #85 source
`mode_CR_n_n_closed` clauses for CR left prefixes `1,0`, `1,1`, and
`1,≥2`; its empty-list bump is also wrong. The theorem `growth76` is an
`rfl` proof of the incorrect projected function only. It is not an authentic
stack-system identity and must not be used as a premise for a raw TM proof.

See [Agent 12's critical correction](../../communications/broadcast/20261122T0813Z_agent12-critical-CR-branch-withdrawal.md)
and the [source-branch audit](../../communications/agent48/20261122T0815Z_agent12-urgent-CR-branch-withdrawal.md).

## Exact discrepancies

Pinned source file
`google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`,
`M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean`, lines 928–953:

- CR prefix `1,0`: source outputs `CR(L8, (0,0)::bumpPairHead^3 R)`, cost 5; first-coordinate form `CR(r, 0::bumpN(R,3))`.
- CR prefix `1,1`: source outputs `EL(bumpPairHead L8, (1,0)::(0,0)::R)`, cost 16; first-coordinate form `EL(bump(r), 1::0::0::R)`.
- CR prefix `1,b`, `b>=2`: source outputs `DR((b-2)::L8, (1,0)::(0,0)::R)`, cost 15; first-coordinate form `DR((b-2)::r, 1::0::0::R)`.

Pinned `Stack.lean` lines 64–67 define
`bumpPairHead []=[(0,0)]`, so the first-coordinate empty bump is `[0]`,
not `[1]`.

The current projected function instead uses different L/R updates for all
three CR cases and `bump []=[1]`. A corrected replay no longer reaches the
advertised endpoint after 76 successors. The old 76/254 count and the root
prefix/growth checkpoint based on it are withdrawn.

## What remains useful

The file is preserved as a record of the failed projected model and its Lean
computation. Its `rfl` proof demonstrates only that the stated function
computes its own claimed endpoint. It does not validate the source transition
system. The separate source-accurate direct D-countdown sweep is documented
in [Agent 12's RootCountdownSweep.md](../agent12-cryptid-root-invariant/RootCountdownSweep.md);
that recurrence uses CR-left-zero and CR-empty, not the mistranscribed
CR-left-one branches, and remains unproved in Lean.
