# Historical full research log

**Unabridged snapshot of the former research README, 6 November 2026.** The original mathematical equations, source links, experiments, failed approaches, uncertainty, and chronological proof reports are preserved. Any “pending” or “current” claims below describe the old writing time. For current synthesis use the [maintained README](README.md).

---

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

## 2026-11-03 deeper result: an eight-pulse, two-digit blank-root trap

**Major local strengthening, theorem still source-mirrored:** [S4Trap.lean.xz.b64](S4Trap.lean.xz.b64), decoded SHA-256 `1cd994153762128b702c2f2e81009710abe3473d463bc28d1fbe40b51f8cb8a0`, imports the previous `S4Phase` module. Both locally compiled on Lean 4.36.0-rc2 and the following theorems' `#print axioms` are exactly `[propext, Quot.sound]`, with no `sorryAx`.

After **56 exact high-level steps from the published root**, the model reaches `C(3,[5,7,7,19,42,12,8,5])` (kernel theorem `first56`). Define the period-eight pair `pairAt(n)` as:

| n mod 8 | First two tail digits after fixed `5,7` | Full next four-step return guaranteed? |
| ---: | --- | --- |
| 0 | `7,19` | Yes |
| 1 | `6,15` | Yes |
| 2 | `8,21` | Yes |
| 3 | `9,28` | Yes |
| 4 | `7,20` | **Unknown; possibly halts on first step** |
| 5 | `6,13` | Yes |
| 6 | `8,19` | Yes |
| 7 | `9,26` | Yes |

**`actual_pair`: for all natural `n` and all actual successful modeled runs of length `56+4n`, the precise reachable state is `C(3,5::7::pairAt(n).1::pairAt(n).2::T)` for some finite T.** The proof imports the genuine modeled blank-root checkpoint, follows each of the eight *universal* two-digit return laws, and uses an arbitrary-stack five-digit right-suffix lemma `epoch_pre5`.

**`actual_seven_eighths_continue`:** for every such surviving return with `n mod 8 != 4`, the next four high-level steps are guaranteed to exist. **`actual_only_hazard_return`:** if the model reaches state `s` at `56+4n` and `highNext s = none`, necessarily `n mod 8 = 4`. These are **genuine-start, arbitrary-time restrictions on the original-shaped acceleration**. They make no claim about the existence or nonexistence of a halting event at the remaining exceptional phase.

For the only potentially halting pair `7,20`, apply the already derived odd power gate at normalized `C(3,5::7::7::20::T)`. Since `weighted(7::20::T)=47+4weighted(T)` and `|7::20::T|=|T|+2`, the exceptional gate is exactly:

```text
13 + weighted(T) + 2^length(T) is a power of two.
```

This last gate simplification is an algebraic application of Agent7's existing one-epoch predicate, **not** a newly source-compiled power-gate theorem. The remaining challenge is to prove that the actual recursively sampled `T` never meets that predicate (or construct an actual reachable witness). This reduces the live arithmetic hazard to one of eight four-step return sectors, substantially stronger than the original one-digit 6/8/9/7 phase filter.

### How the eight laws are proved

The safe 6- and 8-head laws are exact affine updates on the next digit `b`: `(6,b)→(8,b+6)` and `(8,b)→(9,b+7)`. The 9-head pairs `(9,26)→(7,19)` and `(9,28)→(7,20)` and the `(7,19)→(6,15)` pair all terminate their source-style epoch in the even branch and therefore succeed for **every remaining tail**. The `(7,20)→(6,13)` pair is proved **conditionally on success**, using the unbounded suffix-preservation lemma `epoch_pre5` through potentially arbitrarily many odd drains. A synthetic `(7,20)` with carefully chosen tail can still halt, so the exceptional branch must retain its conditional quantifier.

To reproduce: decode both Base64/XZ files; compile `S4Phase.lean` to `S4Phase.olean`; then compile `S4Trap.lean` with that compiled module on the Lean search path. The `#print axioms` audit covers the exact theorems `S4.first56`, `S4.actual_pair`, `S4.actual_seven_eighths_continue`, and `S4.actual_only_hazard_return`. Both source files are independently verified to match their committed compressed bytes via byte-length and FNV-1a fingerprints in addition to local SHA-256; a full original-source kernel import remains an open source-validation step.

**No BB(6) value, bound improvement, or decided holdout is claimed.** The older Agent7 normalized first-register cycle and Agent34 ranked source proofs are reused as context; the two-digit eight-pulse trap is a new local derivation within this repository, without external novelty audit.

## 2026-11-03 exact 32-step reduction and genuine-root halting equivalence

**Strongest current local result:** [S4Return.lean.xz.b64](S4Return.lean.xz.b64), decoded SHA-256 `269cbc8e8792022e2ecfae11c893c0299c51b190fcb6db2e52f9c04681a3d9ba`, imports the two preceding Lean modules. Compiled locally with Lean 4.36.0-rc2; the complete theorem `S4.blank_halts_iff_reduced` reports only **`[propext, Quot.sound]`** and no `sorryAx`. The source model remains a *textually exact, locally proved mirror* of DeepMind's published accelerated definitions; original-source kernel import CI is still pending.

The original-shaped accelerated six-state blank root has been rigorously reduced **within the standalone model** to a *single partial map on a list of natural numbers*. Define `bumpBy k` by the original `k`-fold stack-head increment (an empty list becomes `[k-1]` when `k>0`). Define

```text
dangerous(T) =
  Option.map (fun state => state.leftStack.drop 4)
    (epoch 27 T [0,6,5,3,1])

reduced(T) = Option.map (bumpBy 17) (dangerous(bumpBy 31 T))

initial_reduced_stack = [42,12,8,5]
```

The universal theorem **`S4.thirtytwo_exact`** states, for *every finite stack T*, including synthetic ones and arbitrary large numbers:

```text
run 32 (C(3,[5,7,7,19] ++ T))
 = Option.map (fun U => C(3,[5,7,7,19] ++ U)) (reduced(T)).
```

This identity includes the halting case: if `dangerous(bumpBy31 T) = none`, the original-shaped high-level run fails during that 32-step block, and `run 32` is `none`. The proof factors its eight four-step returns into `sixteen_safe` and `sixteen_dangerous`; both are exact arbitrary-tail Lean equalities. The entire first half consists of safe stack-head increments `+13` then `+18`, totaling `+31`; the second half contains a single potentially failing `epoch 27` and a final head increment `+17`.

**`S4.blank_conjugacy`** proves, for every natural `n`:

```text
run (56+32*n) (C(3,[0]))
 = Option.map
     (fun T => C(3,[5,7,7,19] ++ T))
     (reducedRun n [42,12,8,5]).
```

Finally **`S4.blank_halts_iff_reduced`** proves the *full halting equivalence*, with correct quantifiers and no finite horizon:

```text
(there exists k such that run k (C(3,[0])) = none)
  iff
(there exists n such that reducedRun n [42,12,8,5] = none).
```

The reverse direction uses the absorbing property of a failed `Option` run and the fact that any eventual original failure must also be visible at a sufficiently later 32-step checkpoint. The forward direction follows by direct model conjugacy. **This is a strict exact reduction of the entire remaining blank-root problem**, rather than a trace extension or a classification of synthetic terminal cylinders.

### Why this changes research priorities

The previously published source S4 return map has an unbounded left digit stack and a right stack. The new `reduced` map has a single arbitrary finite list, with deterministic head increments by 31 and 17 around **one residual `epoch 27`**, and starts from the four-digit seed `[42,12,8,5]`. This provides a concrete candidate for a compact invariant, arithmetic conjugacy, inverse-image grammar, or optimized verified simulator. All halting possibilities in the resulting eight-pulse cycle pass through one conditional gate with the `7,20` head prefix. A proof of nonhalting of `reduced` from the seed would decide this single authentic DeepMind holdout, conditional on a completed original-source semantic bridge.

**Limit:** the equivalence is proven against copied, inspected source equations and **not yet kernel-bridged to the unmodified DeepMind `highLevelNext`**. It does not resolve `reduced` from its seed, much less BB(6). Moving it into `results/` or claiming original-machine certification would be premature. To reproduce, first compile the decoded `S4Phase.lean` and `S4Trap.lean` to their matching `.olean` modules; then compile the decoded `S4Return.lean` with both import files available on the Lean module search path.

## 2026-11-03 scalar head factor and affine safe branch

Two additional locally kernel-checked modules continue the above reduction:

- [S4Head.lean.xz.b64](S4Head.lean.xz.b64), decoded SHA-256 `2556caac3ad0c90308779d50f4a78485c4770cbc3a360c3ceb6201fa951ee078`. It imports `S4Return` and proves a six-digit right-suffix preservation lemma, the universal *conditional* first-digit law, and the genuine-reduced-seed all-time cycle.
- [S4Odd.lean.xz.b64](S4Odd.lean.xz.b64), decoded SHA-256 `2110a4dfcbe4befe8016c3a8be6d2931b8b7df2afc9ec58260d79c83331d968c`. It imports `S4Head` and proves the **unconditionally successful affine branch** for every odd first digit.

Define `H(b) = floor(b/2) + 39 + 3*(b mod 2)`. `S4.reduced_head` proves, for **every** finite nonempty list `b::R`, if `reduced(b::R)=some U`, then `U = H(b)::T` for some T. The proof handles arbitrary-long odd drains on even b, via the new `epoch_pre6` right-suffix lemma. This is an exact *factor map on the first list digit*, conditional only on the one unresolved possibility that the reduced operation returns `none`.

The kernel computes the first five genuine-seed reduced iterations exactly:
```text
T0 = [42,12,8,5]
T1 = [60,30,36,5]
T2 = [69,41,41,44]
T3 = [76,98,41,44]
T4 = [77,79,60,52,28,25]
T5 = [80,140,60,52,28,25]
```
The `S4.reduced_first5` theorem certifies T5; the intermediate entries are independently computed exact arithmetic checks.

Then `S4.actual_reduced_head_cycle` proves that for every `n`, if the genuine reduced run exists at index `5+n`, the first digit is the explicit period-four function:

| n mod 4 | First digit of reduced list |
| ---: | ---: |
| 0 | 80 |
| 1 | 79 |
| 2 | 81 |
| 3 | 82 |

The periodicity follows from the *universal* `H` law, with `H(80)=79`, `H(79)=81`, `H(81)=82`, and `H(82)=80`.

**Strongest unconditional case:** `S4.reduced_odd_exact` proves for every odd `b` and every finite `R`, with no success assumption:
```text
reduced(b::R) =
  some ((floor(b/2)+42)::bumpBy(floor(b/2)+23, R)).
```
Thus at two of every four *surviving* reduced-return positions after T5, with first digit 79 or 81, the entire next reduced step is unconditionally defined. The even-digit positions 80 and 82 remain the only possible residual halting gateways in that persistent period-four regime. The arithmetic is based on the original source-shaped `epoch` definitions. Both modules report solely standard Lean axioms and no `sorryAx`.

These theorems provide a precise compact dynamical system with an explicit scalar factor and a separate partial tail update. **They do not prove survival at the even-digit gateways**, and they have not undergone original DeepMind source-module import validation.

## 2026-11-03 partial exact even-head return

The sixth local Lean module, [S4Even.lean.xz.b64](S4Even.lean.xz.b64), raw SHA-256 `5aab323784fccfeae01129f4b1a0258fdf9f90137f7337d579a133438aa0f0b7`, builds on `S4Odd`. Lean 4.36.0-rc2 prints only `[propext, Quot.sound]` and no `sorryAx` for `S4.reduced_even_favorable`.

For every **even** first digit `b`, arbitrary second digit `c`, and arbitrary remaining list `R`, if `c+b/2+23` is even then the complete reduced step is provably safe and has the exact affine form, with `k=(c+b/2+23)/2`:
```text
reduced(b::c::R) = some((b/2+39)::(k+2)::bumpBy(k,R))
```
The theorem covers empty R as well as unbounded nonempty R. Combined with the previously proved odd-head branch, **the sole unresolved potential halting cases after reduced step five are**: first digit 80 with **even** second digit; or first digit 82 with **odd** second digit. All 79 and 81 first-digit steps are unconditionally safe; the complementary 80-odd and 82-even steps also have exact unconditional successful return formulas. These are necessary hazard conditions, not proof that any such actual state halts.

This additional result further partitions the authenticated blank-seed orbit in a second-digit parity test and provides explicitly computable updates where the parity permits a direct even exit. It remains a local proof in a source-mirrored model pending original module import.

## 2026-11-03 strongest theorem: full blank halting iff two sparse exceptional sectors

The last two new files strengthen the phase analysis to a complete **all-time halting equivalence** with two explicitly identified exceptional prefix phases. Both compile locally with Lean 4.36.0-rc2, no `sorry`, and all printed axioms exactly `[propext, Quot.sound]`. They remain proofs about the exact source-mirrored S4 high-level map, without an original-module kernel import.

- [S4Pair.lean.xz.b64](S4Pair.lean.xz.b64), decoded SHA-256 `0246ce3a74f844239dda8397463e8f8ea65af47c0b037f18852dd4fb61ac5d49`. Import `S4Even`. A universal arbitrary-stack theorem `reduced_pair` computes the first two output digits from the first two input digits whenever the reduced step succeeds. Let
```text
P(b,c) = if b odd then (b/2+42, c+b/2+23)
         else (b/2+39, floor((c+b/2+23)/2)
                          + (if (c+b/2+23) even then 2 else 0))
```
Then `reduced(b::c::R) = some U` implies `U` begins with `P(b,c)`, for **all finite R**. The odd-even unfavorable case uses a new seven-suffix preservation theorem `epoch_pre7` for arbitrary-depth odd drains. The first nine authentic reduced steps reach `[80,147,228,133,28,25]`.
- `S4.actual_pair_cycle` proves that **for every n**, if the modeled genuine reduced execution survives to index `9+n`, the first two digits follow this period-eight cycle:
  
| n mod 8 | First two digits | Next reduced step guaranteed? |
| ---: | --- | --- |
| 0 | (80,147) | Yes |
| 1 | (79,107) | Yes |
| 2 | (81,169) | Yes |
| 3 | (82,232) | Yes |
| 4 | (80,150) | **Unknown** |
| 5 | (79,106) | Yes |
| 6 | (81,168) | Yes |
| 7 | (82,231) | **Unknown** |

This is a true seed-dependent **all-time inductive result**. The theorem `actual_only_two_hazard_phases` establishes that a reduced transition can fail **only at n mod 8 = 4 or 7** after the first nine reductions, never at any other phase. The other six transitions are universally safe for all deeper stack tails, because of `S4Odd` and `S4Even`.
- [S4Hazard.lean.xz.b64](S4Hazard.lean.xz.b64), decoded SHA-256 `3f706cc63a6361affe95fc47880aaa150e9b739a4a95f317a0af12c1983dba25`. Import `S4Pair`. Its theorem `S4.blank_halts_iff_two_exceptional_gates` proves the **exact universally quantified blank-halting biconditional** in the source-shaped model:
```text
(∃k, run k C(3,[0]) = none) ↔
(∃n s, (n mod 8 = 4 or n mod 8 = 7)
       and reducedRun (9+n) [42,12,8,5] = some s
       and reduced s = none).
```
This accounts for every finite early step via the kernel-checked first-nine prefix and uses `none` absorption correctly. Each reduced step corresponds to exactly 32 original-shaped high-level steps after the 56-step prefix. At the **first** remaining two gates, the reduction starts from original modeled high-level indices `56+32*(9+4)=472` and `56+32*(9+7)=568`; later candidate gates recur at strides of eight reduced steps or **256** high-level steps.

**Research consequence:** A genuine proof excluding failure at the two recursive tail families `(80,150)::R` and `(82,231)::R` sampled by the actual orbit would decide the S4 machine, provided the original-source import is certified. The synthetically possible failure cases remain, and neither an actual halting witness nor all-time nonhalting invariant has been established. This is a structural mathematical reduction, not a BB(6) bound or external publication novelty claim.

**Verification:** Decode all eight `.lean.xz.b64` files in dependency order (Phase, Trap, Return, Head, Odd, Even, Pair, Hazard) and compile with matching Lean 4.36.0-rc2 modules on `LEAN_PATH`. The verified source bytes are documented by their SHA-256 fingerprints above.
