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


## New complete E 1100 branch and exact conditional halting cylinder (09:57 UTC)

The original six-state D-start Cryptid has new source-verified E-return and halting families, universally quantified over k and arbitrary trailing binary suffix y.

- [EZeroPair.lean](./EZeroPair.lean): **q=0** branch `I_(3k+4)(0 1100 y)` returns after exactly `12k²+49k+96` steps to `I_(8k+3)(0 1111 0 101010 y)`. This is a genuine distinct branch compared with Agent35's E-(10)^q1100 for q≥1. The proof uses an exact 60-step E-to-B turn with a symbolic arbitrary left alternating stack and Agent32's existing universal left sweep.
- [EAllDouble.lean](./EAllDouble.lean): for **every q≥0**, a single exact original-machine E return theorem `all_e_double` covers both the q=0 case and Agent35's source-verified q≥1 case. The companion `all_e_double_implicit_blank` formalizes the physical-tape return when the final two zeros are supplied by the infinite blank tape, using the source-level `ObsEq` semantic bridge. The result is a complete **specified pattern family**, without claiming every possible E suffix is classified.
- [EZeroHalt.lean](./EZeroHalt.lean): the precisely guarded input `I_(3k+4)(0 1101100 y)` enters the original machine's frozen terminal state 6 **for the first time** at exactly `12k²+41k+99` steps. Universally valid for every k and suffix y. `full_E_zero_exact_first_halt` proves exclusion of every earlier time, using a certified state-5 configuration at step 65 after the E boundary and absorption of frozen state 6. A weaker supposed all-suffix `11011` trigger is demonstrably false; the two following zeros are essential for the all-suffix cylinder. The k=0 base example appears in earlier @-d research, so external novelty is unestablished.

**Original-source Lean 4.36.0-rc2 successful checks:**
[EZeroPair CI 41422953241](https://github.com/FlareZ123/bb6/actions/runs/41422953241),
[EZeroHalt exact-first-time CI 41424490768](https://github.com/FlareZ123/bb6/actions/runs/41424490768),
[all-q E/implicit-blanks CI 41424743730](https://github.com/FlareZ123/bb6/actions/runs/41424743730).
Every final theorem has `[propext, Quot.sound]` only, no `sorryAx`. All workflow runs compiled the unmodified SHA-checked original Agent31/Agent35 modules and exact new sources. All artifacts remain intermediate in `im-results/`. None proves that these patterns arise on the actual blank-start orbit, or determines BB(6).

## Original-source strict first return for E-(10)^q110111 (3 November 2026)

[**E110111First.lean**](./E110111First.lean) strengthens Agent37's existing source-certified all-q endpoint [E110111Pairs.lean](../agent37-root-language-pilot/E110111Pairs.lean) to an exact **first physically valid** F/0 section return for every k,q≥0 and arbitrary finite Boolean y:

```text
I_(3k+4)(0 (10)^q 110111 y)
  --[12k² + 49k + 68 + 4q primitive steps]-->
I_(8k+3)(longPacket(q,y)).
```

The endpoint uses Agent37's original `longPacket` definition. The new theorem `BB6.Agent32E110111First.full_E_110111_first_return` additionally proves that at every positive primitive time strictly below the given duration, the machine is **not simultaneously** in state F, scanning zero, with its entire physical left tape empty. Its boundary lemma `eLong_firstPhysical` proves this for the entire unbounded E turnaround for all m,q,y, including the reverse C walk and final D sweep.

The distinction is necessary: the six-step C-to-D turnaround can visit state F on an **interior** nonempty-left configuration. An initially attempted stronger no-F statement was false and was corrected using the exact physical-return predicate; the first CI run exposed the distinction. The proof reuses Agent2's strict original-source E prefix and B-sweep checks and Agent37's quantified E endpoint, proving the remaining first-return guard by induction and finite local checks.

**Authentic original-source [GitHub Actions CI 41739674447](https://github.com/FlareZ123/bb6/actions/runs/41739674447) succeeded**, compiling original SHA-restored `Boundary.lean`, unchanged Agent32 `CryptidSix` and `CryptidPairs`, unchanged Agent37 `E110111Pairs`, unchanged Agent2 `PrefixENoFSource` and `NoEarlierF`, and the new module under Lean 4.36.0-rc2. The two printed theorem axiom audits are exactly `[propext, Quot.sound]`, with no `sorryAx`. Reproduce via the **manual-only** workflow [agent32-e110111-first.yml](../../.github/workflows/agent32-e110111-first.yml). No per-commit CI trigger was introduced.

This source-certified theorem refines a genuine first-return transition rule and may be reused when composing symbolic F-section itineraries. No proof connects this entire cylinder to a true blank-origin visit, no complete D-machine decision follows, and BB(6) remains open. All findings remain intermediate.
