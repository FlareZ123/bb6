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

The all-time corollary `one_digit_all_time_complete` quantifies over every finite horizon `n`, establishing universal synthetic-tail nonhalting if and only if every one-digit extension survives forever. **Original-source Lean verification succeeded** in [manual CI run 42345755016](https://github.com/FlareZ123/bb6/actions/runs/42345755016), including direct import and proof of the source `S4Toggle.prun` recurrence.

### Exact horizon-wide growth characterization

The subsequent [S4MultiGrowth.lean.xz.b64](S4MultiGrowth.lean.xz.b64), also **original-source certified** in [CI run 42346135479](https://github.com/FlareZ123/bb6/actions/runs/42346135479), proves a stronger and simpler equality for every finite `T` and `n`:

```lean
(∀ S, S4Toggle.prun n (T++S) ≠ none)
  ↔ ∃ U, S4Toggle.prun n T = some U ∧ U.length ≤ T.length+1
```

This is `all_suffix_iff_short`. The all-time corollary `all_time_iff_bounded` states that **every finite suffix survives forever precisely when the unextended stack survives forever and its length always remains at most one entry above its initial length**. The proof uses the previously sourced all-depth sharp guard, the general valuation/length law, and the fact that successful chains cannot shrink the stack; no numerical cutoff, digit cap, or unproved liveness assumption appears. The conclusion is strictly about the infinite family of *synthetic* suffixes. It does not establish a genuine S4 blank-tape outcome.

## Proof mechanism

Write `k=|T|`, `W(T)=Σᵢ (Tᵢ+1)2ⁱ`, and `ν₂(v)` for the exact power of two dividing a positive integer `v`. The proofs use the unmodified source `H` and `G` definitions. Every odd input to `H` emits a digit and carries `b+⌊a/2⌋+1` to the next digit; the first even carry ends the drain. For `G c T=some U`, the pre-existing source-derived stack-length identity is

`|U| = max(|T|, ν₂(W(T)+c)+2)`.

In particular, every successful drain is nonshrinking. If the potential `W(T)+c` is divisible by `2ᵏ`, that successful drain outputs at least `k+2` digits; otherwise its output is bounded by `max(|T|,k+1)`. This is the first bridge from dyadic arithmetic to exact output length, generalized through arbitrary finite positive-offset drain sequences in `chain_good_short` and `chain_bad_long`.

If `W(T)+c` is **not** divisible by `2ᵏ`, `H_suffix_stable` and `G_suffix_stable` prove that every appended suffix `S` survives that drain, with a common first `k` output digits and an exact affine weighted shift of `2ᵏW(S)`. More generally, define two stacks `x,y` to be `(k,t)`-coupled if they have the same first `k` digits and `W(y)=W(x)+2ᵏt`. Under a safe modular gate, `G_pair_stable` proves that their successful outputs are again `(k,t)`-coupled. The invariance persists through any finite chain and any finite number of returns as long as each bare-input guard succeeds.

Now suppose the first unsafe gate in a chain encounters a potential `A=W(x)+c` divisible by `2ᵏ`. Let `q=A/2ᵏ ≥1`; choose `r` so that `2ʳ>q`, and set `d=2ʳ-q-1≥0`. A one-symbol appended suffix `[d]` has weighted increment `2ᵏ(d+1)`, making the dangerous potential exactly `2ᵏ(q+d+1)=2ᵏ⁺ʳ`. The exact binary-power stopping theorem therefore forces that gate to return `none`. Coupling transports the same digit `d` through all earlier *safe* gates, even those whose output lists have grown. The constructive `chain_bad_weight` / `chain_bad_one_digit` lemmas formalize this argument with no bounded-digit or bounded-length hypothesis.

For a **finite horizon of n returns**, fix the protected depth `k=|T|` once at the starting stack. Define `nGood(k,n,T)` by applying `P` to the bare stack `n` times, requiring the modular guard at **that same fixed k** at every intermediate return. If the guard ever fails, the preceding coupling argument constructs a one-digit extension of the *original* stack that stops no later than return `n`. If all guards pass, every extension survives all `n` returns. This is the quantified `all_suffix_iff_nGood` theorem, transferred by `runN_eq_prun` to the exact source `prun`; `one_digit_horizon_complete` and `one_digit_all_time_complete` follow.

Finally, the actual unextended `P` output length is nondecreasing across successful returns. If all guards at the fixed initial `k` pass, every intermediate stack has length at most `k+1`; conversely, if any guard fails while the bare orbit survives, that stage forces length at least `k+2`, permanently. Hence a **single final-length check** is equivalent to the entire sequence of fixed-depth modular guards:

```
All finite suffixes survive n returns from T
  iff prun(n,T)=some U and |U| <= |T|+1.
```

Quantifying this statement over every `n` gives the all-time theorem. None of these equivalences requires or grants a blank-origin reachability property for a constructed suffix.

## Verification, reproducibility, and boundaries

All four modules import the repository's exact source-connected `S4Toggle`, `S4Octet`, `S4PowerGate` chain. The manual [agent7 S4 source workflow](../../.github/workflows/agent7-s4-original.yml) builds pinned unmodified Google DeepMind Cryptids `c86f15861709b76042998c5211c7b2f83991621b`. Source-reproducible successful runs are: [all-depth sharp 42343695742](https://github.com/FlareZ123/bb6/actions/runs/42343695742), [Boolean and phase 279 42344162653](https://github.com/FlareZ123/bb6/actions/runs/42344162653), [sharp growth 42344827178](https://github.com/FlareZ123/bb6/actions/runs/42344827178), [one-digit iff growth 42345293076](https://github.com/FlareZ123/bb6/actions/runs/42345293076). The multi-step [run 42345755016](https://github.com/FlareZ123/bb6/actions/runs/42345755016) and growth-horizon [run 42346135479](https://github.com/FlareZ123/bb6/actions/runs/42346135479) also succeeded against the same pinned source. Every listed job checks decoded SHA-256 fingerprints and compiles in Lean with only standard axioms and no custom gate axiom.

Decoded Lean SHA-256 digests: `S4AllDepthSharp` = `5c055cc0fdd6bb40c7e189080c126277e32510d7d0b9ca55162264c512a5e115`; `S4AllDepthGrowth` = `3fbb97be0a309ccad35bbd957c5efaf90e3eb95b2a5ac3c70623a92f4850f3bd`; `S4MultiSharp` = `587894ae875e731f86cde19d79e07db0ec84574ee61e8be1f82bc130427639b7`; `S4MultiGrowth` = `eb6a757cf2ebd0a3ece9b5e1881c7dcfc9bc7ec9b970ba6dada55ff6c90b5d0f`.

The standalone [checker.py](checker.py) is a minimal deterministic source-shaped one-digit witness extractor. [horizon_checker.py](horizon_checker.py) implements the fixed-k finite-horizon guard. It reproduces a synthetic appended digit `1043` which makes the six-digit genuine reduced seed halt after 18 returns, while the unextended seed remains alive with length 10. This is a modeled, alternate *input* only, never a blank-tape halt witness. [root_guard_scan.py](root_guard_scan.py) reproduces a finite simulation of **1,000,000 successful triple-drain returns** from the genuine reduced seed `[301,650,645,322,163,160]`: five guard-unsafe steps, precisely those with ≥2-entry growth; one additional safe 1-entry growth. This is **finite computational evidence**, with no unlimited orbit theorem. The earlier generic tests covered 24,000 random prefixes and 1,554 small exhaustive prefixes. A reproducible [seeded horizon regression](horizon_regression.py) checks 25,000 variable-depth/variable-horizon cases using seed `0xB6106`, verifies every unsafe case's specific one-digit halter, and probes four random suffixes for each safe case. These remain computational sanity tests of the source-shaped implementation.

## Rejected shortcut: odd-quotient monotonicity

The original reduced seed's first seven simulated guard exposures (through 200 million `P` returns) have odd quotients `1787, 5875, 70271, 822257, 141780809, 3969557963, 5465684189`, which happen to increase. This is **finite exploratory simulation**; it establishes no unrestricted growth invariant. Moreover, [odd_part_nonmonotonic.py](odd_part_nonmonotonic.py) independently reproduces a **synthetic four-head-sector counterexample**: starting at `[280,1903,4054,46,1286,3315]`, successive guard exposures at returns 68 and 210 have odd quotients **14,307 then 13,559**, a strict decrease. A monotonic-odd-part proof derived only from the four-head phase cycle is therefore false. Any genuine-root proof must use finer information about authentic tail/history.

## Genuine-root obstacle and prior work

The original S4 blank-machine halting question is equivalent, through the repository's already source-checked reduction, to eventual failure of `P` on the **actual** orbit of `[301,650,645,322,163,160]`. The orbit's suffix is determined by its complete earlier history. One-digit forcing alternatives are **synthetic** and do not establish genuine reachability, a machine halt/nonhalt verdict, or any bound on the BB(6) champion.

The next meaningful step is a history-sensitive invariant ruling out the exact `W+c=2^e` gate on every actual growing stack, or a genuine halting witness. Existing relevant work: [six-digit sharp atlas](../agent5-s4-sharp6/README.md), [prefix causality](../agent5-s4-prefix-causal/README.md), [early-stop completion](../agent5-s4-general-sharp/S4EarlyCompletion.lean), [Agent 7 fixed-prefix obstruction](../agent7-s4-prefix/README.md), and [stack-length law](../agent5-s4-length/README.md). These are intermediate internal theorems; external academic novelty has not been established, so the dossier remains in `im-results/`.
