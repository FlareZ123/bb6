# S4: exact universal suffix risk, growth, and one-digit completeness

**Intermediate original-source-certified research, 7 November 2026.** Every finite chain of positive-offset S4 odd drains admits a complete, executable all-suffix safety test. Its failure is always demonstrated by **one appended synthetic digit**. More strongly, a successful bare-stack chain admits an unsafe completion exactly when its output length rises by at least two entries. All statements quantify over arbitrary finite stack prefixes and offsets. This strictly generalizes the earlier six-digit, 1,024-phase sharp atlas without assuming genuine blank-root reachability. **Neither the authentic S4 machine nor BB(6) has been decided.**

## Exact source semantics and main results

Let `W([])=0`, `W(b::T)=b+1+2W(T)`. The original S4 source-shaped odd drain is `G(c,[])=H(c-1,[])`, `G(c,b::T)=H(b+c,T)`, with `H` defined in [S4PowerGate](../agent5-s4-length/S4PowerGate.lean). The exact positive-offset stopping theorem, already source verified in [S4Octet](../agent5-s4-octet/S4Octet.lean), is `G c T=none ↔ ∃e, W(T)+c=2^e`. A finite `chain cs T` applies these drains consecutively. For the authentic S4 reduction, `P T=chain [509,290,219] T`.

Define `good cs k T` recursively: every stage must have `(W(current)+c)%2^k≠0`, produce `some next`, and satisfy the same requirement on the remaining offsets. The **all-depth sharp theorem** [S4AllDepthSharp.lean.xz.b64](S4AllDepthSharp.lean.xz.b64) establishes, for all positive-offset chains and all finite `T`:

```lean
(∀ S : List Nat, chain cs (T++S) ≠ none)
  ↔ good cs T.length T
```

The [Boolean adapter](S4AllDepthBool.lean), `s4_triple_sharp_bool`, proves this condition equivalent to the terminating `guardB [509,290,219] T.length T`. It also handles the old exceptional phase 279 without a literal witness.

The **exact growth theorem** [S4AllDepthGrowth.lean.xz.b64](S4AllDepthGrowth.lean.xz.b64), `chain_sharp_growth`, sharpens the criterion: whenever `chain cs T=some U`, the finite guard is true **if and only if** `U.length≤T.length+1`. Thus the source-specific corollary `s4_P_growth` makes universal suffix safety exactly equivalent to a single successful bare-stack `P` transition whose length increases by at most one.

The [synthetic completion theorem](S4AllDepthSurvival.lean), source-checked `s4_one_digit_halt_iff_growth`, combines the sharp guard, the exact stack-length law, and constructive binary-power completion:

```lean
P T = some U →
  ((∃ t : Nat, P (T++[t])=none) ↔ T.length+2≤U.length)
```

There is no fixed cutoff or bound on digits or list lengths. In particular, a growth jump of at least two is *precisely* an opportunity for an alternative, one-digit appended stack to stop at the next transition. It says nothing about the already-fixed actual tail.

## Quantified finite-horizon extension

[S4MultiSharp.lean.xz.b64](S4MultiSharp.lean.xz.b64) proves a further generalization locally in Lean. Let `runN n T` denote `n` consecutive source-defined `P` returns, proved equal to the existing `S4Toggle.prun`. Define `nGood k n T` by checking the same fixed `k`-bit guard at every consecutive unextended `P` state for `n` returns. The theorem `all_suffix_iff_nGood` proves

```lean
(∀ S, runN n (T++S) ≠ none) ↔ nGood T.length n T.
```

In addition, `one_digit_horizon_complete` proves for **every finite n**:

```lean
(∀ S, prun n (T++S) ≠ none) ↔
(∀ t : Nat, prun n (T++[t]) ≠ none).
```

The all-time corollary `one_digit_all_time_complete` quantifies universally over `n` on both sides. It reduces synthetic **universal** nonhalting over all finite suffixes to the one-parameter family of one-digit extensions. This does *not* reduce the genuine blank-root orbit to that family. **At present this multi-step file is locally compiled with a definition-matched S4 interface, and an unchanged-source CI run has been dispatched; do not describe it as original-source certified until successful.**

## Proof mechanism

The odd drain preserves a fixed `k`-digit prefix and the weight increment `2^k t` between coupled stacks whenever the source stopping potential is nonzero modulo `2^k`. This affine coupling composes through arbitrary finite odd-drain chains and repeated returns. When the earliest safety guard fails, choose a positive `t` making the relevant stopping potential exactly a binary power. Appending the one-digit list `[t-1]` to the original prefix realizes that weight increment at the first step and preserves it through every safe preceding stage.

Separately, the [S4Length length law](../agent5-s4-length/README.md) gives the exact output length of each successful odd drain in terms of its 2-adic valuation. The valuation passes the designated prefix length exactly when a new two-or-more-entry burst appears, which proves the growth characterization. These proofs apply to *every* successful input, including arbitrary zero digits and potentially arbitrarily long odd-carry drains.

## Verification, reproducibility, and boundaries

All four modules import the repository's exact source-connected `S4Toggle`, `S4Octet`, `S4PowerGate` chain. The manual [agent7 S4 source workflow](../../.github/workflows/agent7-s4-original.yml) builds pinned unmodified Google DeepMind Cryptids `c86f15861709b76042998c5211c7b2f83991621b`. Source-reproducible successful runs are: [all-depth sharp 42343695742](https://github.com/FlareZ123/bb6/actions/runs/42343695742), [Boolean and phase 279 42344162653](https://github.com/FlareZ123/bb6/actions/runs/42344162653), [sharp growth 42344827178](https://github.com/FlareZ123/bb6/actions/runs/42344827178), [one-digit iff growth 42345293076](https://github.com/FlareZ123/bb6/actions/runs/42345293076). These check actual decoded SHA-256 hashes and compile Lean against the pinned source, with standard Lean axioms and no custom gate axiom.

Decoded Lean SHA-256 digests: `S4AllDepthSharp` = `5c055cc0fdd6bb40c7e189080c126277e32510d7d0b9ca55162264c512a5e115`; `S4AllDepthGrowth` = `3fbb97be0a309ccad35bbd957c5efaf90e3eb95b2a5ac3c70623a92f4850f3bd`; `S4MultiSharp` = `587894ae875e731f86cde19d79e07db0ec84574ee61e8be1f82bc130427639b7` (multi-step local compile succeeded, original-source run pending).

The standalone [checker.py](checker.py) is a minimal deterministic source-shaped one-digit witness extractor. [root_guard_scan.py](root_guard_scan.py) reproduces a finite simulation of **1,000,000 successful triple-drain returns** from the genuine reduced seed `[301,650,645,322,163,160]`: five guard-unsafe steps, precisely those with ≥2-entry growth; one additional safe 1-entry growth. This is **finite computational evidence**, with no unlimited orbit theorem. The earlier generic tests covered 24,000 random prefixes and 1,554 small exhaustive prefixes.

## Genuine-root obstacle and prior work

The original S4 blank-machine halting question is equivalent, through the repository's already source-checked reduction, to eventual failure of `P` on the **actual** orbit of `[301,650,645,322,163,160]`. The orbit's suffix is determined by its complete earlier history. One-digit forcing alternatives are **synthetic** and do not establish genuine reachability, a machine halt/nonhalt verdict, or any bound on the BB(6) champion.

The next meaningful step is a history-sensitive invariant ruling out the exact `W+c=2^e` gate on every actual growing stack, or a genuine halting witness. Existing relevant work: [six-digit sharp atlas](../agent5-s4-sharp6/README.md), [prefix causality](../agent5-s4-prefix-causal/README.md), [early-stop completion](../agent5-s4-general-sharp/S4EarlyCompletion.lean), [Agent 7 fixed-prefix obstruction](../agent7-s4-prefix/README.md), and [stack-length law](../agent5-s4-length/README.md). These are intermediate internal theorems; external academic novelty has not been established, so the dossier remains in `im-results/`.
