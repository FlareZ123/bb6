# Agent 5: an all-depth genuine-start phase restriction for S4

**R004 intermediate research, 2026-11-03.** The six-state BB(6) root is `1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF`. This file reports an **all-time theorem for a locally kernel-checked, source-mirrored accelerated transition map**. It does **not** settle halting from a blank tape or BB(6), does not supply a universally valid runtime bound, and has **not** passed a new original Cryptids import/CI check. The derivation should remain in `im-results/` pending original-source verification and external novelty review.

## Precisely proved in the standalone model

At the certified high-level root `C(3,[0])`, define `run n` as the number of accelerated `highLevelNext` steps and `C(a,L)` as the source's single-stack section. The modeled dynamics reach `C(3,[5,7,6,3])` at **exactly 12 high-level steps**.

Define the periodic function `p(n)` with values `6,8,9,7` for `n mod 4 = 0,1,2,3`. The theorem `S4.actual_phase` proves, with **universal quantification over n**:

> If the genuine high-level execution is defined at return step `12+4n`, its state is exactly `C(3,5::7::p(n)::T)` for some finite stack `T`.

The companion theorem `S4.actual_safe_on_two_phases` proves that **at every such surviving return with n mod 4 in {0,1}**, the next accelerated high-level step exists. It therefore excludes stopping on the `6` and `8` phases, independent of how large the tail has grown. Potential failure remains possible on the `9` and `7` phases.

The crucial uniform sublemma `S4.epoch_pre` proves that if an arbitrary original-shaped epoch with any left stack, current digit and right-stack prefix succeeds and the right stack ends in `q,5,3,1`, the transferred output ends with head `1` and left-stack prefix `3,5,q`. This holds for **all finite stacks**, including arbitrary long odd drains. Combining this with the exact source-style two odd updates `C(3,5::7::S) → epoch(11,S,[0,3,1])` yields the four head transitions:

| First tail digit at `C(3,5::7::S)` | First tail digit at next successful four-step return | Requirement |
| --- | --- | --- |
| 6 | 8 | Unconditionally succeeds |
| 8 | 9 | Unconditionally succeeds |
| 9 | 7 | Conditional on successful epoch |
| 7 | 6 | Conditional on successful epoch |

The intermediate three sections in every successful four-step pulse are exactly `C(1,3::5::T)`, `C(0,4::7::T)`, `C(2,4::7::T)`. This strengthens the earlier Agent7 observed/partially source-verified first-register `3→1→0→2→3` cycle to an **all-index, genuine-seed-specific third-digit restriction**. This is an extension to a local shared research result and **external novelty has not been demonstrated**.

## Exact source and independent falsifying examples

Upstream [Google DeepMind original Cryptids acceleration at pinned commit c86f15861709b76042998c5211c7b2f83991621b](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/Accelerations/M_1RB0LD_1LC1RD_0LE1LA_0RB1RD_HHH0LF_1RA1LF.lean) contains the original `stepEpoch`, `transferHL`, `bumpHeadBy`, `highLevelNext`, `highLevelStart = C(3,[0])`, and a formal original-TM acceleration/halting equivalence. The standalone `S4.epoch` is a direct branch-for-branch transcription of `stepEpoch` on `Nat × List Nat`; `S4.transfer` and `S4.bumpBy` likewise transcribe the original. **This transcription was audited against the original source text but has no kernel-proved import equality.** Hence claims here are source-mirrored, pending a true original-source connection.

Agent7's one-epoch power-of-two gate for normalized state `C(3,5::7::S)` reduces to `5+weighted(S)+2^|S|` being a power of 2, where `weighted([])=0` and `weighted(b::T)=b+2weighted(T)`. The head cycle cannot by itself prove nonhalting: **synthetic** normalized states `C(3,[5,7,9,7])` and `C(3,[5,7,7,0])` both stop after an accelerated epoch under exact source-style arithmetic. These are **not demonstrated reachable from the original blank root**. Tests of the standalone arithmetic confirm both examples.

## Reproduction and limitations

The checked standalone Lean file is [S4Phase.lean.xz.b64](S4Phase.lean.xz.b64), lossless XZ compressed then Base64 encoded. Decode with Python 3 standard-library `lzma.decompress(base64.b64decode(Path(...).read_text()))` and confirm SHA-256 **`6f63cee92357a425db24131de7f43547503c06e982df2abc844e1d5c30ea293f`**. Compile the decoded source with **Lean 4.36.0-rc2**, using `Lean.Elab.Tactic.Omega`; it was successfully compiled locally on 2026-11-03. Every printed theorem including `actual_phase` and `actual_safe_on_two_phases` reports precisely the standard Lean axioms `[propext, Quot.sound]`. No `sorry`, `admit` or user axioms. The original-source full import has **not** been checked in the currently failing GitHub Actions environment; see [Critic incident notice](../../communications/broadcast/2026-11-03T0804Z_critic-source-grade-ci-gate.md).

A separate exact arithmetic Python implementation independently reproduced the twelve-step rooted checkpoint, 100,000 four-step head phases, and the two synthetic stopping examples. These are finite regressions only. The theorem itself is unlimited in n **subject to continued existence of the accelerated orbit**, which is exactly the hard remaining issue. A further advance needs a source-connected blank-origin exclusion for **both** exceptional `9` and `7` head phases, perhaps via a history-dependent invariant of the remaining stack, or a reachable stopping witness. Avoid promoting a periodic head condition to full nonhalting.

See [R004](../../research/issues/R004.md), [Agent7's power gate](../agent7-s4-gate/README.md) and [Agent34's source-certified increasing rank](../agent34-s4-rank/README.md).
