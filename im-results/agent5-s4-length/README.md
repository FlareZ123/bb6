# S4 exact stack-length law from 2-adic valuation

**Agent 5, 2026-11-04. Intermediate mathematical result.** This dossier concerns the one-list compact S4 return transducer and its binary weight. It does not decide whether the genuine six-state S4 blank orbit halts, and it does not determine BB(6). The original Cryptids raw-machine/source-accelerator transport remains distinct from this theorem's checked-in source-shaped compact-transducer bridge. External mathematical novelty has not been established.

## All-input theorem

Define the little-endian weight `W([])=0` and `W(b::T)=b+1+2W(T)`. Let `F = compactNext`, the total `List Nat → Option (List Nat)` already studied by Agent 3 in [S4 weighted drift](../agent3-s4-weighted-drift/README.md), which corresponds in the copied S4 model to Agent 5's full 32-high-level-step reduced map. For any `T,U : List Nat` with `F T = some U`, let

```text
W(T)+45 = 2^k (2t+1),       k,t : Nat.
```

Then exactly

```text
U.length = max T.length (k+2).
```

This is the statement of `S4Length.source_compact_length` in [S4LengthBridge.lean](S4LengthBridge.lean), proved for **every finite input stack**, including `[]`, arbitrary zero digits, and arbitrary successful odd-drain depth. No assumptions of blank-root reachability are involved. The factorization holds for the positive integer `W(T)+45` with `k=v₂(W(T)+45)`.

Consequently: successful transitions never decrease the list length. A successful step preserves length `n` exactly when `k ≤ n-2`, and grows to length `k+2` exactly when `k ≥ n-1`. In particular, a *successful* encounter with the necessary halting congruence `2^n | W(T)+45` grows the stack by **at least two digits**. That congruence does not ensure actual halting: the exact synthetic one-step halting condition is that `W(T)+45` itself be a power of two (Agent 8, [exact gate](../agent8-s4-gate/README.md); Agent 7, [prefix obstruction](../agent7-s4-prefix/README.md)).

## Proof

The auxiliary source-shaped function `H(a,L)` recursively consumes odd heads and one left-stack digit, or halves an odd head with empty left stack, until its first positive even head. On even head with nonempty `L=b::S`, it emits `[a/2+2,b+a/2]++S`, **including `a=0`**. On even head and empty `L`, a zero head fails and a positive even head emits two digits. The empty-stack odd `a≤1` case fails.

Define `P(a,L)=a+1+2W(L)`. Every odd branch halves `P` **exactly** while adding one output digit. In any successful even branch, `P` is odd. If an even branch occurs while at least one input digit remains, the output length is `L.length+1`. If all input digits are drained first, successive empty-left odd branches continue for the remaining `v₂(P)` factors and the terminal even branch emits two digits. This yields the general law

```text
H(a,L)=some U, P(a,L)=2^k(2t+1)
   ⇒ U.length = max (L.length+1) (k+2).
```

The Lean proof constructs the four-case inductive evaluation relation `Done`, proves `H_to_done`, and proves `done_length` by structural induction on that relation. The compact initial state obeys `P=W(T)+45` for every nonempty `T`, and the `[]` case is checked separately. The final `bump17` preserves output length on successful nonempty outputs.

The source adapter proves `H_eq_original`, `W_eq_original`, `bump17_eq_original`, and `F_eq_original` **against the unchanged `S4WeightedDrift.lean` imported from Agent 3**, rather than merely comparing finite traces.

A correction during development matters: a first local transcription incorrectly returned `none` for even `a=0` with nonempty `L`; Agent 3's source succeeds there. The model was repaired **before** the final source-connected verification. The final Lean theorem explicitly permits `q=0` in its even/nonempty rule. Any earlier local transcript of the draft must not be cited as authoritative.

## Reproduction and evidence

- [S4Length.lean](S4Length.lean): standalone all-input theorem `F_length`, using Lean 4.36.0-rc2. `#print axioms`: exactly `[propext, Quot.sound]`; no `sorryAx`.
- [S4LengthBridge.lean](S4LengthBridge.lean): imports `S4WeightedDrift` and `S4Length`, proves `source_compact_length`; the final Lean axiom audit is exactly `[propext, Quot.sound]`.
- Manual [source-shaped CI run 41772967621](https://github.com/FlareZ123/bb6/actions/runs/41772967621) at checkout commit `7eb7e8c20a7c1d7b6df52606104c97528cb9cf09` completed successfully. Its actual compile step checked the **SHA-256 pinned, unchanged** `S4WeightedDrift.lean`, then both committed theorem files. [Workflow](../../.github/workflows/agent5-s4-length.yml) is manual-only; no per-commit trigger.
- Independent Python implementation checked the identity for **179,691 successful synthetic random transitions** (lengths 0–8, digits 0–299, fixed random seed 6042026) and **150,000 modeled seeded transitions**. Computation is supplementary; the quantified proof is the Lean theorem. At an earlier step, the Python model also had the zero-head/nonempty transcription issue, so its initial cross-check should be treated as supplementary only; the source-matched Lean CI is decisive.

## Interpretation and remaining obstacle

This supplies an exact infinite-input link between the 2-adic near-halt statistic and the list depth. It is more precise than the already-known strict **weight** growth of the compact return transducer, and complements the prefix-compatible synthetic halting completions. It does not bound the number of steps spent at a fixed depth, and it does not rule out a future **exact power-of-two** value of `W(T)+45` on the true seeded orbit.

Most useful follow-ups: formalize the suffix emitted at a length-expansion event in terms of the odd part `2t+1`; determine whether any genuine-seed history-sensitive invariant controls those odd parts; and, for stronger provenance, compose the existing source-shaped compact transport with the previously source-CI-verified original Cryptids S4 return equivalence in one unchanged-source verification job. Avoid duplicating Agent 3's weighted-growth theorem, Agent 7's fixed-prefix obstruction, or the existing general power-of-two gate.
