# Sharp blank-root right-run law and five physical return families for auxiliary #119

**Established 9 November 2026, original auxiliary-source Lean 4.36.0-rc2.** On the genuine blank-root orbit of the literal six-state auxiliary table `1RB---_1LC1LF_1LD0LC_0LE1RF_1RA1LA_1LB0RD`, every reached B/0 configuration with left bits `t(h−3)=1` and `t(h−2)=0` has **four consecutive ones immediately to the right of the head**. The constant **four is sharp**: [Root119Sharpness.lean](Root119Sharpness.lean) proves a genuine blank-start witness after **1,289** primitive instructions (B/0 at head **−33**) satisfying the same left context with right prefix `11110`. The proof computes the literal original `run 1289 blank` by kernel `decide` and transports it into genuine `Reach`; the witness theorem has only `propext` as an axiom. Both directions passed [original-source CI 42717638415](https://github.com/FlareZ123/bb6/actions/runs/42717638415), with no `sorryAx`.

Four earlier all-parameter physical B/0 return families preserve the forbidden-`1100` left-of-head shield under their explicit input hypotheses. A newly source-checked **fifth family** composes two consecutive odd F/1 waves that return immediately to B/0, with no additional alternating retreat. The first four families' input predicates cover all 49 intervals left unclassified in the older ten-million-step replay; **that coverage is finite evidence**. Neither the new right-run obstruction nor the return families establish an all-time partition of every reachable B/0 configuration. Historical root #119 and BB(6) are still unresolved.

## All-time original blank-root theorem

Write `Reach d` for the *original* inductively defined reachability from blank, with `d=(B,h,t)` and `t(h)=0`. The theorem [`reached_B0_left10x_right1111`](Root119AncestryTen.lean) proves

\[
 \operatorname{Reach}(d)\land t(h-3)=1\land t(h-2)=0
 \quad\Longrightarrow\quad
 t(h+1)=t(h+2)=t(h+3)=t(h+4)=1.
\]

The hypothesis places no restriction on `t(h−1)` or the exterior tape. Two source-imported inverse obstructions support the result:

1. [`Root119Ancestry.lean`](Root119Ancestry.lean) exhausts three primitive predecessors. Under B/0 and `t(h−2)=0`, a length-three predecessor chain forces the immediate three right cells to be marked; the few early blank-run configurations are excluded directly.
2. [`Root119AncestryTen.lean`](Root119AncestryTen.lean) proves a stronger **universal ten-step impossibility**: no ten consecutive original primitive instructions from any source tape can end in B/0 with `t(h−2)=0` and right-hand word `1110` at `h+1,…,h+4`. The finite-predecessor proof exhausts original states and reads backwards through the exact writes. The theorem `reach_has_run` converts any `Reach` proof into a definite primitive count; splitting counts below ten from an arbitrary ten-step suffix gives the genuine-root result `reached_B0_exposed_no_right1110`. Combining it with the three-right-cell property proves the four-right-cell theorem.

**Sharpness from the actual blank orbit.** The source-certified [`original_blank_right_four_is_sharp`](Root119Sharpness.lean) has an existential endpoint with `Reach` and the same left hypotheses, right four ones, and a zero at the fifth right cell. Its witness is the primitive configuration at time 1,289; no synthetic or conditional tape is used. Therefore the above universal conclusion cannot be strengthened from four to five immediate right marks in this genuine-root sector.

**Immediate mathematical consequence for prior return formulas.** In Agent42's exact [even and odd-even B/0 prefix laws](../agent42-root119-guard/EVEN_WAVE_PREFIX_FAMILIES.md), the input left suffix is `101`, hence this theorem applies. The even family has right one-run `2n+1`, so its parameters `n=0,1` are impossible at genuine blank-reachable inputs; the odd-even family has right one-run `2n`, so its `n=0,1` inputs are likewise impossible. Larger parameter values, including dangerous odd-even shield boundaries, are still open. The source-exact ten-step exclusion itself is independent of `t(h−3)=1` and applies to every reached B/0 with `t(h−2)=0` and right word `1110`.

## Exact conditional theorem inventory

For `c=(B,h,t)` with `t(h)=0` and natural parameters `n,m`, let `1^k` denote k consecutive tape ones.

| Source theorem | Exact primitive return time | Return head | Conditions and preserved exterior |
| --- | --- | --- | --- |
| `left_gateway_return n` | `14+2n` | `h−8−2n` | Left suffix `t(h−7..h−1)=0100111`, extended alternating word `(10)^n` from `h−8` leftward ending at a zero; all tape at or left of return head unchanged |
| `left_gateway_B_return n` | `14+2n` | `h−8−2n` | Left suffix `0101001`, same alternating extension and zero sentinel; all tape at or left of return head unchanged |
| `right_gateway_return n` | `12+2n` | `h+2n+2` | Left three bits `000`, right `1^(2n)00`; all tape at or right of return head unchanged |
| `double_sweep_return n m` | **`4n+2m+6`** | **`h−2m`** | `t(h−1)=0`, `t(h−2)=1`, right `1^(2n)0`, and a left `m−1`-pair alternating B/1,F/0 retreat ending at zero, `m≥2`; all tape at or left of return head unchanged |
| [`imm_two_wave_exact n m`](Root119ImmediateTwoWave.lean) | **`4n+4m+20`** | **`h−4`** | B/0 left suffix `101`, nine-step F/1 entry, two individually specified odd F/1 right-wave conditions with an intermediate B/1 move; the returned state is B and the entire tape at or left of `h−4` is unchanged. If the input has `t(h−4)=0`, it is B/0 and its left-of-head shield transfers |

The four original inventory rows have B/0 endpoints under their local tape hypotheses. The fifth is an exact B-state endpoint; the additional source theorem `imm_two_wave_endpoint_shield` proves it is **B/0** when the original cell `t(h−4)=0`, with shield transport. Every step count is in ordinary Turing machine transitions. Exterior tape is universally quantified; no special blank tape outside the listed input corridor is assumed. The double sweep composes a literal 3-step B/0 → F/1 prefix, `n+1` rightward F/1,D/1 pairs, a single F/0 turn to B/1, and `n+m` leftward B/1,F/0 pairs. It is genuinely **two-parameter and unbounded in both directions**. Exact arithmetic is `3 + 2(n+1) + 1 + 2(n+m) = 4n+2m+6`.

The source-certified shield theorems `left_gateway_shield`, `left_gateway_B_shield`, `right_gateway_shield`, and `double_sweep_shield` each conclude existence of that precise physical return with `NoLeft4 true true false` whenever the input has the respective corridor hypotheses and satisfies `NoLeft4 true true false`. Left gateways and the double sweep preserve the entire tape below the returned head. The right gateway shield is proved by an additional induction: each rightward F/D pair writes alternating `01`, and the four-step final tail writes two ones, excluding any newly created left-of-head `1100`.

The new source-[verified immediate-two-wave result](Root119ImmediateTwoWave.lean) is a separate fifth closure. The first wave takes `4n+5` steps from the nine-step B/0 entry, the B/1 bridge takes one step, and the second takes `4m+5`; the sum is `4n+4m+20`. The end head is `h−4`. Both wave tapes, plus the initial four-cell prefix write, agree with the input tape at every coordinate `x≤h−4`, giving unconditional left exterior preservation and, if input reads zero at that boundary, full `NoLeft4` transport. [Original source CI 42719548110](https://github.com/FlareZ123/bb6/actions/runs/42719548110) compiled the two-wave exact law and shield lemma under unmodified Agent42 imports without `sorryAx`.

In an independent 300-million-step raw replay, twelve reached B/0 states with left suffix `110101` all had an immediate preceding B/0 return of the two-odd-wave form: previous left suffix `01010101`, input right run `2n`, right terminal `010101`, elapsed `8n+28` steps and head shift `−4`, with output right run `2n+8` and the same terminal `010101`. For example, from time `3,191,647` to `3,193,243` the input right run had length 392 (`n=196`), the two F waves had parameters `196,198`, and the output run length was 400. The twelve observations are finite, not a classification of every reached unsafe boundary. They identify a plausible source mechanism for the unresolved odd-even sentinel guard without establishing global closure.

## Verification against untouched original definitions

The manual [.github/workflows/agent12-root119-corridor.yml](../../.github/workflows/agent12-root119-corridor.yml) checks [`Root119Ancestry.lean`](Root119Ancestry.lean), [`Root119AncestryTen.lean`](Root119AncestryTen.lean) and [`Root119Sharpness.lean`](Root119Sharpness.lean) against unmodified original `Root119Gate.lean`, `Root119BShift.lean`, `Root119BShield.lean` from [Agent42](../agent42-root119-guard/README.md). It then checks the three original-source checksum-pinned return modules. All declarations use the literal `BB6Root119.next`, physical signed tape, and exact `run`; no `sorryAx` is admitted.

**[Original-source Lean 4.36.0-rc2 success, run 42717638415](https://github.com/FlareZ123/bb6/actions/runs/42717638415)** verifies the universal reachability theorem, its authentic sharpness witness, and all four return families. The ten-step exclusion, genuine-root restriction, sharpness witness and four-right theorem print only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound` where used). The earlier [return-only successful run 42588104760](https://github.com/FlareZ123/bb6/actions/runs/42588104760) is retained for source provenance.

| Source | Source status | Scope |
| --- | --- | --- |
| [`Root119Ancestry.lean`](Root119Ancestry.lean) | Readable, compiled against original imports | Genuine reachable B/0 right-three property; arbitrary three-step inverse |
| [`Root119AncestryTen.lean`](Root119AncestryTen.lean) | Readable, compiled against original imports | Arbitrary ten-step inverse contradiction and all-time blank-root right-four theorem |
| [`Root119Sharpness.lean`](Root119Sharpness.lean) | Readable, original-source kernel computation of 1,289-step blank run | Genuine reached B/0 with right `11110`, proving optimality of four |
| [`Root119ImmediateTwoWave.lean`](Root119ImmediateTwoWave.lean) | Readable, independent [source CI 42719548110](https://github.com/FlareZ123/bb6/actions/runs/42719548110) | Exact two-wave `4n+4m+20` endpoint, left exterior preservation and shield transport |
| [`Root119Corridor.lean.xz.b64`](Root119Corridor.lean.xz.b64) | Decoded SHA-256 `65efa8844d8836f2579e4d7d5a71f308a2fc2f5343a0c0309f1f0c971ca2ab1d` | Three one-parameter B/0 returns, exact tape boundaries |
| [`Root119CorridorShield.lean.xz.b64`](Root119CorridorShield.lean.xz.b64) | Decoded SHA-256 `0888e541438f09ef9da1ea7228d51a2446c488a3b3c42a40a955354acec023ef` | Three corresponding forbidden-word shields |
| [`Root119Cross.lean.xz.b64`](Root119Cross.lean.xz.b64) | Decoded SHA-256 `f5dd3f8e6432dec762dbecc1b8c7a791330218bf6c21be4b599fb457606ef99d` | Two-parameter double sweep with shield |

## Independent finite trace correspondence

[The standalone Node.js CommonJS 10M test](test-root119-corridors.cjs) simulates all six literal state rows from the blank tape, identifies corridor hypotheses at actual B/0 states, checks that **the next** B/0 arrives at exactly the proved formula's time and position, and audits `NoLeft4 true true false` at inputs and returns.

| Parameterized family | Observed 10M B/0 first returns | Previously unclassified by Agent42 |
| --- | ---: | ---: |
| First left | 21 | 19 |
| Second left | 10 | 10 |
| Right | 18 | 18 |
| Double sweep | 2 | 2 |
| **Total** | **51** | **49** |

The two first-left family starts at raw time 1,275 and 3,638 had already been classified by prior macros; the other 49 are exactly the outstanding `other` set in the existing 10M [Agent42 first-return audit](../agent42-root119-guard/README.md). Every one of 51 observed family inputs and outputs satisfied the shield in the replay.

The two formerly exceptional double-sweep instances instantiate the exact theorem at:

- Start time **4,208**, input B/0 head **−68**, parameters **`n=16, m=9`**; return in **88** steps at head **−86**.
- Start time **1,450,177**, input B/0 head **−779**, parameters **`n=368, m=28`**; return in **1,534** steps at head **−835**.

This census is reproducible and matches original-source machine semantics, but no finite replay is an all-time proof.

## Missing global proof obligation

Agent42's original [`blank_halts_iff_gate`](../agent42-root119-guard/Root119Gate.lean) reduces auxiliary blank-root halting to a genuinely reached D/0 with two left ones. The `NoLeft4 true true false` shield and five exact conditional return theorems would be useful toward excluding this gate, but no proof yet establishes that **all** genuine B/0 returns satisfy the necessary corridor hypotheses or preserve the shield. In particular, the odd-even family with `n≥2` has a sharp, source-checked `110` left boundary obstruction; whether authentic reachability excludes that boundary remains open.

A useful next research target is an inductively closed, source-exact language for all B/0 input sections, including two-wave chains, alternating left retreats, right-run endings, and exceptional predecessors. The new all-time four-right restriction narrows that language, but supplies no global upper bound for BB(6) or nonhalting theorem for #119.

