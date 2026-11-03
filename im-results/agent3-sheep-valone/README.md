# Sheep even-return valuation hubs and coherent low-valuation corridors

**Agent 3, R010, 2026-11-03. Classification: intermediate mathematics.** The six-state Sheep machine, the authenticated blank start, and BB(6) remain undecided. This dossier gives a locally kernel-checked property of the published section arithmetic and an explicit synthetic halting-family construction. There is no new claim of external academic novelty.

## Source and exact semantics

The rooted table is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. The established blank-section trajectory is `5 → 7 → 10`. For `t=2^a u` with odd `u`, the nonterminal one-variable Sheep map is `F(t)=t+a+3` when `u=3` and `F(t)=t+a+(u−1)/2` when `u≥5`; it halts at pure powers of two. The first-even-return map `E` follows one F step by all forced odd-return steps. When F(t) is already even, E(t)=F(t).

Original Turing machine semantics and equivalence of the authentic blank halt event to a power-of-two encounter in the even orbit starting at 10 were source-verified previously by Agent 16, manual [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). The Lean files here restate the exact published section `Step` in isolation; their own source-import CI has **not** been run during the current GitHub Actions incident.

## Result A: every positive output valuation from one source valuation

For every integer `b≥1` there is a legal genuine **single** generic Sheep first-even return `E(x)=y` with `v₂(x)=1` and `v₂(y)=b`. The source can be made arbitrarily large. Thus the graph on positive 2-adic valuations induced by actual *legal synthetic* even-state transitions has a directed edge from valuation 1 to **every** positive valuation. This is an all-parameter exact statement.

**Explicit construction.** Put `S(q)=(16^q−1)/5`, which is integral because `S(0)=0` and `S(q+1)=16S(q)+3`. For `b=4q+r`, choose:

| r | w | odd target cofactor c | restriction |
|---|---|---|---|
| 0 | `3S(q)` | 3 | `q≥1` |
| 1 | `18S(q)+3` | 9 | none |
| 2 | `28S(q)+5` | 7 | none |
| 3 | `88S(q)+17` | 11 | none |

Every row satisfies `w≥2`, `5w+3=2^b c` and `c` odd. Set `x=2(2w+1)`. Its odd part is at least 5, its exact valuation is one, and the genuine generic return is `F(x)=5w+3=2^b c`. The output is already even, so E(x)=F(x). In fact each constructed w is odd, hence every source lies in the single class `x≡6 (mod 8)`.

For each `N≥0`, replacing `w` with `w+2^(b+1)N` replaces `c` with `c+10N`. The latter stays odd and proves arbitrarily large genuine source witnesses with the same exact output valuation.

**Global invariant consequence.** Let `P` be *any* subset of the positive valuation indices, without periodicity, computability, or regularity assumptions. Suppose an invariant on legal even section states is exactly `I(t) ⇔ P(v₂(t))`, contains seed 10 (whose valuation is one), and is preserved under every legal nonterminal even-return edge. Applying the constructed valuation-one edge for each b forces P(b) for all b≥1. The invariant therefore includes every possible halting power `2^b`. This rules out that entire globally inductive invariant class, including arbitrary nonperiodic functions of a single unbounded valuation. It places **no** restriction on a proof that exploits exact blank-root history or the full integer value.

**Lean certificate.** [SheepValuationComplete.lean](SheepValuationComplete.lean) proves `all_target_valuations` and `valuation_only_invariant_full` for every b and every P in the exact standalone `Step` relation, with Lean 4.36.0-rc2. Local `#print axioms` reports only `[propext, Quot.sound]`, with no `sorry`, `admit`, or `native_decide`. The stronger arbitrarily-large-witness lift is a direct written arithmetic corollary, not separately kernel certified. [verify_valuation_fan.py](verify_valuation_fan.py) independently checked 8,000 exact arithmetic edges, for all b=1..2000 with four shifts per b. Each returned value was compared against both literal F and the first-even closed formula.

## Result B: long exact valuation-one corridors, including halting endpoints

For `L≥1` and any odd `v≥5`, define `X_i=2(5^i·4^(L−i)·v−1)` for `0≤i≤L`. Direct substitution into the original generic section formula yields, for every `i<L`,

`F(X_i)=E(X_i)=X_(i+1)`, with `X_i≡2 (mod 4)` and `X_L≡0 (mod 4)`.

Consequently the genuine first-even-return map has uninterrupted corridors of **arbitrary finite length** whose nonterminal sources all have exact valuation one. The complete parametric `Steps` theorem and both modular assertions are locally kernel checked in [SheepValOne.lean](SheepValOne.lean); each printed axiom list is exactly `[propext, Quot.sound]`.

Moreover, every L has such a corridor **ending at a pure halting power**. Set `n=6·5^(L−1)` and `v=(2^n+1)/5^L`. This v is an odd integer at least 5. For integrality, start from `x_1=64`, `x_(k+1)=x_k^5`: since `5|x_1+1`, and for `x≡−1 (mod 5)` the factor `(x^5+1)/(x+1)=x^4−x^3+x²−x+1` is divisible by 5, induction shows `5^L | 64^(5^(L−1))+1=2^n+1`. The quotient is odd; the elementary growth of powers shows it is at least 13. The endpoint then satisfies `X_L=2(5^L v−1)=2^(n+1)`. This last universal 5-adic construction is a **written exact arithmetic proof** accompanying the kernel-certified corridor map, not itself a Lean theorem.

The independent [verify_valone.py](verify_valone.py) checked all exact F/E returns and halting targets for L=1..6 (21 edges), plus 360 other arbitrary odd-seed corridor edges. These starts are freely chosen and have no established connection to the actual start 10.

## Interpretation and limitations

These methods expose two specific barriers to overly coarse nonhalting proofs: the complete valuation-one outgoing fan and arbitrarily long valuation-one corridors that can end in halting states. Both are about actual legal transitions from **synthetic source integers**. They do not show that the fixed blank-origin even orbit ever reaches a constructed source, and cannot decide the Sheep machine. An invariant using exact initial-state history, high 2-adic digits, 3-adic coupling, or additional counters can evade both obstructions.

Prior research already shows broader finite-modulus quotient mixing: [Agent 22's coherent-orbit theorem](../agent22-sheep-mixed-hub/COHERENT-ORBIT.md), [Agent 40's no-Presburger corollary](../agent40-sheep-coherent-audit/NO-PRESBURGER-INVARIANT.md), and [Agent 17's forward 3-adic construction](../agent17-sheep-forward/README.md). The valuation-only theorem addresses the distinct **unbounded exact valuation** abstraction, which need not be Presburger-definable. It makes no assertion that either approach is novel beyond the repository.

Next possible extension: classify whether arbitrary finite prescribed **valuation histories** occur along one genuine synthetic even orbit, rather than using a changing representative per edge. Any claim about the authentic blank orbit must additionally preserve its exact root 10.


## Result C: complete arbitrary finite positive-valuation language

The stronger [VALUATION-WORDS.md](VALUATION-WORDS.md) theorem is now locally **fully kernel checked** in three further Lean modules: [SheepOddInverse.lean](SheepOddInverse.lean), [SheepGeneralVal.lean](SheepGeneralVal.lean), and [SheepValuationWords.lean](SheepValuationWords.lean). They prove that **every finite list of positive exact 2-adic valuations is realized, in order, by one coherent trajectory of genuine legal generic Sheep first-even returns**, and that the set of suitable synthetic initial section integers contains a whole arithmetic progression. The certified intermediate theorem `ValWord.any_positive_word` has only `[propext, Quot.sound]` axioms under local Lean 4.36.0-rc2. Source-level semantic reuse remains the earlier externally certified published F/E equality; no new GitHub CI validation occurred.

The mathematical consequence is that no universal restriction on finite positive-valuation histories alone can hold over **all** legal synthetic generic section trajectories. This is compatible with source-connected, blank-seed-sensitive nonhalting proofs, including invariants based on entire actual orbit histories. The exact blank start 10 is not shown to belong to the constructed cylinder. No Sheep or BB(6) decision, numerical bound, or published-priority claim is made.
