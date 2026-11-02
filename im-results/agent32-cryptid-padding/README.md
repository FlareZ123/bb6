# Agent 32: original-machine infinite-blank padding bisimulation

**Research status:** reusable original-source formal infrastructure, **intermediate**. It does not decide the Cryptid holdout, establish blank halting/nonhalting, or improve a Busy Beaver bound. No claim of external novelty.

## Problem

The original Cryptid six-state machine `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` is encoded by Agent 31's verified original `CryptidBoundary.Cfg` with finite `l, r : List Bool`, scanned bit `h`, and state `st`. Lists are finite representations of semi-infinite tapes filled with zeros. Consequently, `xs` and `xs ++ replicate q false` may denote the **same physical tape** while remaining unequal Lean lists. A symbolic exact-return equality involving a terminal `false` cannot simply be substituted for a genuinely implicit blank suffix by `rfl`.

## Theorems

[`Generic.lean`](./Generic.lean) defines the infinite tape observation `bitAt xs i = (xs[i]?).getD false`; `TapeEq` equates every such bit. It proves for an arbitrary deterministic two-symbol transition table:

```lean
run_pad (delta : Nat → Bool → Option Instr) (n p q : Nat) (c : Config) :
  CfgEq (run delta n c)
    (run delta n ⟨c.left ++ List.replicate p false,
       c.bit, c.right ++ List.replicate q false, c.state⟩)
```

[`BoundaryPadding.lean`](./BoundaryPadding.lean) defines the **exact** Cryptid rule table, with F-on-1 entering the frozen state 6, and proves `source_step` and `source_run` as a semantic equality to Agent31's **unmodified raw machine**.

- `source_congr`: observationally equivalent source configurations remain equivalent after every finite raw-machine run.
- `source_pad`: any far-end all-zero padding on either tape half preserves physical evolution.
- `source_init_pad`: the original `CryptidBoundary.init xs` evolves equivalently to `CryptidBoundary.init (xs ++ replicate q false)` at all times.
- `source_init_halt_iff`: their exact finite-time halt-state-6 indicators agree for all `n,q,xs`.
- `source_chain`: any two exact-interval observational certificates can be composed, allowing physically equivalent but syntactically differing intermediate configurations.
- `source_transport`: exact symbolic macros transfer to all observationally equivalent start and finish configurations.

[`PaddedApplications.lean`](./PaddedApplications.lean) applies the existing source-verified `CryptidBoundary.full_E_pairs` theorem to a **genuinely implicit blank** at the right tape end, for all natural `k,q`. It proves:

```text
I_(3k+4)(0 (10)^q [implicit infinite blank])
  --[12k²+49k+50+4q raw steps, physically]--> 
I_(8k+5)(0 1^(2q+6) [implicit infinite blank])
```

The conclusion is `ObsEq` (infinite-tape semantics), not syntactic equality of the finite lists. This is a logically sound specialization of the existing macro; it is not a new return-word family.

## Reproducibility and trust

- Toolchain: Lean 4.36.0-rc2, standard kernel.
- SHA-verified original upstream `Boundary.lean` from `../agent31-cryptid-boundary/unpack.py`, whose recorded content hash is `0d9f160644d919adf7239b49857fa6cd62ee6cdecadfe0a75ec312a612194883`.
- Manual workflow: [`.github/workflows/agent32-cryptid-padding.yml`](../../.github/workflows/agent32-cryptid-padding.yml); it runs **only** via manual `workflow_dispatch`, never on commits.
- Original-source CI [41419395469](https://github.com/FlareZ123/bb6/actions/runs/41419395469) passed. The core `source_step`, `source_run`, `source_congr`, `source_pad`, `source_chain`, `source_transport` all have axiom audit exactly `[propext]`, with no `sorryAx`.
- The additional initial-padding and E-pairs specialization passed [original-source CI 41419879489](https://github.com/FlareZ123/bb6/actions/runs/41419879489) (2026-11-02 09:21 UTC). The four added theorems `source_init_pad`, `source_init_halt_iff`, `source_chain`, `source_transport` have only `[propext]`, and `full_E_pairs_implicit_blank` has exactly `[propext, Quot.sound]`; no `sorryAx`.

## Why it matters and what it does not imply

This proves an all-time semantic representation invariant and eliminates the common misuse of syntactic tape-list equality when moving between explicit and implicit zeros. The `source_chain` combinator provides a principled route to an actual-blank forward certificate that uses existing unbounded exact macros with possibly different list padding. It **does not** provide a closed reachable-word invariant or prove that the actual blank orbit follows an infinite symbolic return sequence. Existing millions-section computational work by @-d still greatly exceeds the finite conditional itineraries in this repository.


## Universal interleaved token-code return on implicit blanks

Source: [CodeImplicitNil.lean](./CodeImplicitNil.lean). For every natural k and every finite Boolean token word w, encode each false token as 10, each true token as 111, in any order. Let d(w) count false tokens with weight 1 and true tokens with weight 4. Let C(m,w) be the exact primitive transition cost from Agent25's wordCost. Then the original six-state machine returns:

```text
I_(3k+3)(0 Code(w) implicit-blank)
  -> I_(8k+11+2d(w))(implicit-blank)
```

in exactly `12k*k+41*k+32 + C(4k+3,w) + 2*(4k+3+d(w))+6` primitive steps. The conclusion is exact source finite-list equality, with no explicit final zero token. This extends Agent35's source-certified arbitrary encoded-word return, which required an explicit final zero, and Agent37's grouped-pair/triple implicit-blank theorem.

Proof: compose Agent35's `a_code_return` with Agent25's `a_close_nil`, using original-source A prefix and Agent35's all-time semantics bridge to lift the finish back into Agent31. The complete source chain passed [manual CI 41420762660](https://github.com/FlareZ123/bb6/actions/runs/41420762660) against the unmodified SHA-verified upstream originals. The final two theorem axiom audits are exactly `[propext, Quot.sound]`; no extra axioms. Workflow: [agent32-code-implicit-nil.yml](../../.github/workflows/agent32-code-implicit-nil.yml).

This is an intermediate generalization. No closed blank-start nonhalting argument or BB(6) bound follows.


## Packet algebra, inversion cost and source-level confluence

Two new fully original-source verified Lean modules give exact algebraic control of the previously certified arbitrary-codeword family.

[TokenCostNormal.lean](./TokenCostNormal.lean) defines `pairsN(w)` as the number of 10 tokens, `triplesN(w)` as the number of 111 tokens, and `mixedInv(w)` as the number of ordered pairs of positions with a 10 token before a 111 token. Write `T(t)=t(t-1)/2`, encoded as the primitive recursive `triangular`. It proves for **all** words w and every m:

```text
wordInc(w) = p + 4*t
wordCost(m,w) = 2*p + (6*m+41)*t + 24*T(t) + 6*I
0 <= I <= p*t.
```

Consequently the exact primitive cost lies between `2p+(6m+41)t+24T(t)` and that value plus `6pt`. The `wordCost_append` theorem proves the precise cost cocycle, and `swap_cost_context` shows that exchanging a 10 packet immediately preceding a 111 packet reduces the exact cost by six **independently of the preceding and following packet words**.

[CodePermutation.lean](./CodePermutation.lean) combines those theorems with the original-machine `full_A_code_implicit_nil`:

- `swap_times`: the return cost of swapping adjacent 10 and 111 is exactly six steps apart.
- `swap_confluence`: two genuine raw six-state runs, starting from the two differently encoded initial F tapes, reach **the exact same finite configuration**, at their respective exact return times, with a six-step time difference.
- `same_counts_confluence`: for all k and all codewords u,v with the same numbers of both token types, the source-machine trajectories reach the same exact F-return configuration. Their timings need not coincide, and are determined by the inversion formula.

**Full source Lean 4.36.0-rc2 original-source CI [41422121853](https://github.com/FlareZ123/bb6/actions/runs/41422121853) PASSED** 2026-11-02 09:38 UTC. `wordCost_closed`, `wordCost_lower`, `wordCost_upper`, `wordCost_append`, `swap_cost_context`, `swap_times`, `swap_confluence`, `same_counts_confluence` all have precisely standard `[propext, Quot.sound]` dependencies and no extra axioms. The raw machine and token parser were independently restored from the existing SHA-verified original source files.

This gives a reusable **quotient of an entire infinite family of conditional return trajectories by token counts**, and an exact cost correction by word inversion count. No property of a complete infinite blank-start trajectory follows automatically, and no historical priority claim is made.
