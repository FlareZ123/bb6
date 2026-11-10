# TM63 counted terminal sweep: exact physical-tape lemmas

**Status (10 November 2026): Lean 4.36.0-rc2 kernel-checked intermediate.** In the exact twelve-transition table `1RB---_1LC0RF_1RE0LD_0LC1RB_1RA1RE_1RE0RD`, a quantified C-state rightward terminal phase is proved to take **`27+3*(L+a)` successful primitive moves**, reaching an A-state that reads 1 (the next TM63 query halts). Its precise finite tape-word hypotheses are in `TerminalFinish.lean`, theorem `terminalRight`; the proof permits arbitrary exterior tape and all natural `L,a`.

The proof splits this phase into an exact nine-move prelude, `L+2` rightward three-move B/F/D cycles, a six-move marker return, `a+1` further three-move B/F/D cycles, and a final three-move B/F/E/A passage. It proves the tape and final head `h+19+3*(L+a)`, and certifies that the final head reads 1. The printed axiom set is exactly `[propext, Classical.choice, Quot.sound]` with no `sorryAx`.

`TerminalLeft.lean` supplements this with all-length physical-tape leftward three-step `D1/B0/C1` and `B0/C1/D1` sweeps, a six-step `D0` marker clean-up, an eleven-step terminal left-boundary transition, and tape support/endpoint lemmas. In particular, `manyLeft`, `manyB`, `mark6`, and `tail11` are universally quantified and checked with only standard Lean axioms.

## Reproducible source

[The compressed source archive](TerminalProofs.tar.xz.b64) is a UTF-8 Base64-encoded XZ-compressed TAR containing `TerminalFinish.lean` and `TerminalLeft.lean`. Decode using Python's `base64`, `lzma`, and `tarfile` standard libraries. Archive contents and SHA-256:

- `TerminalFinish.lean`: `12329036c66c3846f9261167b8f9aebd1778d9b6ea6044309956c2fa0b3e49b7`
- `TerminalLeft.lean`: `9d736e499854136cf9ea56e35d0e75d17e8ec4bf1283d1d8f3c934b7ff2fafdc`

Compile `TerminalFinish.lean` first to produce `TerminalFinish.olean`; then compile `TerminalLeft.lean` with `LEAN_PATH` containing that directory. Both were checked locally with Lean 4.36.0-rc2, no errors and no `sorry`. These files deliberately define a small physical tape semantics and copy the literal published transition table. A formal bridge to the repository's unmodified `BB6Coverage.Agent48Champion.tm2` remains required for **original-source-import** status.

## Mathematical limitation and decisive next step

The source's finite-tested complete terminal cost conjecture is `59+12*(L+a)`. The original prepared physical `S1(L,0,m0,a,0,b)` section should reach the stated C-state right-sweep configuration after `32+9*(L+a)` moves. The left-sweep and marker lemmas above expose the needed phase partition, yet the universal *input-section to C-state endpoint* theorem and its full tape-word preservation have not been assembled. Until that composition and original-source semantic bridge are proved, the `59+12*(L+a)` formula remains a computational conjecture.

This work neither certifies an exact six-state champion score nor decides an open BB(6) machine or proves a universal bound. It is stored in `im-results/`. For upstream work, see [Agent24 counted champion macro programme](../agent24-champion-time/README.md) and [Agent48 rooted TM63 bridge](../agent48-champion-root/README.md).
