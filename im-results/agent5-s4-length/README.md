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

## Exact final two digits at length expansion (second proved theorem)

The source-matched theorem [`S4SuffixBridge.lean`](S4SuffixBridge.lean), `S4Length.source_compact_terminal_tail`, strengthens the length result. Suppose `compactNext T = some U`, and `W(T)+45 = 2^k(2t+1)`, with `k≥1` and `T.length≤k+1`. Then there exists a list `V` such that

```text
U = V ++ [t+2, t-1].
```

Thus the two final digits at every successful growth by valuation `k≥max(1,|T|-1)` are completely determined by the odd part of `W(T)+45`, including all input zero digits and arbitrarily deep odd drains. They differ by exactly 3. The formula is defined for successful steps; no conclusion about the first failure is smuggled into it. In particular `t=0` cannot arise under these hypotheses, because that would require the power-of-two terminal failure. The `k=0` low-valuation case is excluded since final `bump17` then changes the first of the two output digits.

Proof: [`S4Suffix.lean`](S4Suffix.lean) proves `done_terminal_tail` by induction on the exact `Done` evaluation derivation. The potential `a+1+2W(L)` halves under every odd branch, and when the initial valuation `k` is at least the input list length, every original stack digit is consumed before the positive-even terminal pair. At that point `a=2t` and the pair is `[t+2,t-1]`. `F_terminal_tail` shows the final `bump17` modifies only the leading digit, provided `k≥1`; [`S4SuffixBridge.lean`](S4SuffixBridge.lean) transports the result to Agent 3's unchanged source-shaped compact function. All source files compiled with Lean 4.36.0-rc2 and all final axiom audits contain exactly `[propext, Classical.choice, Quot.sound]`; no `sorry`.

**Manual CI** [41773571439](https://github.com/FlareZ123/bb6/actions/runs/41773571439) **succeeded** against unchanged SHA-pinned original Agent 3 compact helper source and the new theorem sources. This establishes local source-shaped equivalence, not a direct unchanged-upstream Cryptids raw-machine import. External novelty remains unreviewed.

Example: the modeled seed reaches an 18-digit stack at iteration 27,920 with `W(T)+45=2^19·70271`. The next successful output has 21 digits, ending in `[35137,35134]` because `t=(70271-1)/2=35135`. This one finite example is independent numeric illustration only.

A potentially productive further step is to establish an exact all-input value for the **weighted deficit** after expansion, expressed in terms of `k,t` and the consumed digit quotients, and then test whether the actual blank-orbit's sequence of odd parts can ever equal 1. A length and suffix theorem alone does not exclude the root halt gate.


## Original Cryptids source audit completed (2026-11-04, 04:44 UTC)

The original-source import check described as pending in the earlier narrative **has succeeded**. Manual [GitHub Actions run 41774764780](https://github.com/FlareZ123/bb6/actions/runs/41774764780) at repository revision `96cfabc1440fbe25cde2974be6600964bb8c3f39` completed successfully. Its runner-executed step *Check exact original Cryptids epoch against existing compact map* succeeded, after pinning upstream Cryptids `c86f15861709b76042998c5211c7b2f83991621b`, building the unchanged original S4 accelerator, and checking SHA-256-pinned Agent 3 compact sources. It compiled `S4NativeCompact.lean` (including `compact_exact_native_epoch`) and `S4NativeValuation.lean` (including the length and terminal-pair transport). Job `126392440687` reports success for the actual source compilation step.

Thus the exact compact epoch identity and both valuation theorems have now been **Lean checked with the original unchanged Cryptids high-level `stepEpoch` imported**. This is a *per-return* source statement: it does not by itself transport all blank raw-machine steps to the compact seed, close the two exceptional gates, prove S4 nonhalting, or determine BB(6). The original two-gate raw-halt equivalence is independently source-certified in [S4 source bridge](../agent5-s4-source-bridge/README.md). All novelty and rooted-reachability qualifications elsewhere in this dossier still apply.
