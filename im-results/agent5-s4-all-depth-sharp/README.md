# Exact all-depth suffix-safety theorem for S4 odd-drain chains

**Intermediate theorem, 7 November 2026.** For any finite sequence of *positive* offsets, and any finite nonnegative-integer stack prefix, a recursively computed finite guard characterizes exactly when **every possible finite suffix** survives that entire chain of odd drains. Whenever the guard fails, there is a **one-digit synthetic suffix** making the chain fail. This strengthens the six-digit, 1,024-phase sharp atlas [S4SharpCensus](../agent5-s4-sharp6/README.md), and removes its 68-case enumeration from the general proof mechanism. It provides no authentic S4 blank-root halt/nonhalt decision and no BB(6) upper bound.

## Mathematical statement

Use the original S4 compact return's definitions:

- `W([])=0`, `W(b::T)=b+1+2W(T)`.
- `G(c,[])=H(c-1,[])` and `G(c,b::T)=H(b+c,T)`.
- `H` is the exact odd-carry drain in [S4PowerGate](../agent5-s4-length/S4PowerGate.lean).
- `chain [c₁,...,cᵣ] T` applies the indicated `G` maps successively, stopping on the first `none`.

For a prefix `xs` of length `k`, define the finite predicate `good(cs,k,xs)` by recursion through the list `cs`. The empty chain is good. A chain `c::cs` is good exactly when `(W(xs)+c) % 2^k ≠ 0`, the source operation `G c xs` returns `some ys`, and `good(cs,k,ys)` holds.

**Lean theorem `S4PrefixExact.chain_exact_prefix`:** if every offset in `cs` is positive, and each drain has the exact source-certified binary-power stopping gate, then

```lean
(∀ S : List Nat, chain cs (xs ++ S) ≠ none)
  ↔ good cs xs.length xs
```

The theorem is fully quantified over arbitrary prefix lengths, digits, suffixes and positive offset lists. The companion `chain_bad_weight` supplies a constructive *weight offset* for a synthetic one-digit stopping suffix, even when a preceding odd drain consumes the entire chosen prefix. The binary-power gate is the already established `G_none_iff_power` theorem, proved in [S4Octet.lean](../agent5-s4-octet/S4Octet.lean).

**S4 specialization `s4_triple_sharp`:** the exact triple drain `P=G 509 >>= G 290 >>= G 219` satisfies

```lean
(∀ S : List Nat, S4Toggle.P (xs ++ S) ≠ none)
  ↔ good [509,290,219] xs.length xs
```

for every finite `xs`. This theorem supersedes the restriction to six cyclic phases for classifying arbitrary-prefix universal suffix-safety. It does **not** state that any synthetic completion is reachable from the genuine blank start.

## Proof mechanism

The source `H` drain is affine with respect to arbitrary appended suffixes whenever its stopping potential has nonzero residue modulo the designated prefix power of two. This yields `G_suffix_stable`, which proves that successful outputs have a stable `k`-digit prefix and preserve exactly the additional term `2^k W(S)` in weighted output. Two inputs with the same first `k` digits and weights differing by `2^k t` remain coupled under safe `G` operations.

If a chain's guard fails at the earliest stage, that stage's potential is divisible by `2^k`. A positive integer `t` can make the potential a binary power by adding `2^k t`. The coupling theorem transports that exact weight offset across the successful earlier stages, providing a single last digit `[t-1]` that forces the actual chain to stop. This handles arbitrarily late odd drains, including those that consume all `k` original digits.

## Verification and provenance

Lean source is stored in [S4AllDepthSharp.lean.xz.b64](S4AllDepthSharp.lean.xz.b64), XZ-compressed then Base64-encoded. Decode to `S4AllDepthSharp.lean`; decoded SHA-256 is `5c055cc0fdd6bb40c7e189080c126277e32510d7d0b9ca55162264c512a5e115`. It imports `S4Toggle`, itself importing the unmodified repository `S4Octet` and `S4PowerGate`. The S4 upstream source pin in the existing manually dispatched verification workflow is Cryptids `c86f15861709b76042998c5211c7b2f83991621b`.

**Original-source Lean verification: successful.** [Manual CI run 42343695742](https://github.com/FlareZ123/bb6/actions/runs/42343695742) built the SHA-pinned unmodified Cryptids S4 acceleration, source-connected `S4PowerGate`, `S4Octet`, `S4Toggle`, and this theorem at commit `aa9e980fc960204d03b729fa38b2a8dab9b10956`. The runner checked the exact decoded SHA-256 before compilation. The original `G_none_iff_power` theorem now discharges the generic hypothesis. `#print axioms` on the final specialization consequently reports only standard Lean axioms, with no bespoke gate assumption and no `sorryAx`.

An additional source-shaped module [S4AllDepthBool.lean](S4AllDepthBool.lean) proves `guardB_spec` and `s4_triple_sharp_bool`, establishing that one *executable Boolean* guard exactly classifies universal suffix-safety. It also locally kernel-proves a uniform existence proof for the previously exceptional six-digit phase 279 without importing its literal witness. That module compiled locally against a definition-matched source interface; its direct original-source CI check has been dispatched and must complete successfully before it is described as source-certified.

Independent empirical regressions tested 24,000 random prefixes (lengths 1–8) and all 1,554 prefixes of lengths 1–4 using digits 0–5; no mismatch to the proposed finite guard or one-digit witnesses was found. These tests supplement the quantified Lean proof rather than replacing it.

## Exact remaining question

The genuine S4 reduced seed is `[301,650,645,322,163,160]`. Source-connected work proves blank halting iff the genuine `P` orbit eventually fails. The present theorem says every guard-failing finite prefix admits a *synthetic* stopping completion. The actual tail is history-dependent, and an all-time invariant ruling it out remains open. Any attempt at solving S4 must constrain that genuine unbounded tail rather than classify arbitrary completions alone.

Closest prior results: [general prefix causality](../agent5-s4-prefix-causal/README.md), [sharp six-digit atlas](../agent5-s4-sharp6/README.md), [early-drain structural completion](../agent5-s4-general-sharp/S4EarlyCompletion.lean), and [Agent 7 prefix-completion obstruction](../agent7-s4-prefix/README.md). External novelty has not been assessed. The present file belongs in `im-results/` pending proof integration and research-level novelty review.
