# F197: exact mixed-prefix free-monoid reset transducer

**Status:** a new **unbounded, literal six-state source-machine theorem**, accepted by Lean 4.36.0-rc2 (CI [46083890068](https://github.com/FlareZ123/bb6/actions/runs/46083890068)); transitive axioms for `F197.fmFullFamilyClosed` are exactly `[propext, Quot.sound]`, with no `sorryAx`. Formal bit-length consequence in `ATFreeMonoidGrowth.lean` is undergoing its own CI check as of 2026-11-27 23:42 UTC. The result does **not** imply complete F197 blank-tape nonhalting or an exact BB(6) value.

## The theorem

For literal six-state, two-symbol machine

`1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`,

work at the standard reset `B(L,e)` with nearest-first run words, `e=1` on the right. Use `A=(1,1)`, `T=(2,2)`, `P=AAT`, and `Q=TAT`. Let `W=b₁...b_N` be **any nonempty** word over the alphabet `{P,Q}`. Write `p=#P`, `k=#Q`, so `p+k=N`. Define the block morphism

```
F(P) = P=AAT,       F(Q) = AAAT,
F(b₁...b_N) = F(b₁)...F(b_N).
```

Independently choose any nonempty Boolean data `c₀,...,c_q∈{A,T}` for q≥0, and let

```
Z = c₀ (T c₁) ... (T c_q),
H(A)=AT,    H(T)=AAT,
Φ = A H(c₀) ... H(c_q),     t=#{i:c_i=T}.
```

For every arbitrary **run-aligned left-tape continuation X** (its first actual bit is 1), the complete literal source machine has the exact finite nonhalting run

```
B(W Z AA X, e)
    ->^(68p + 82k + 74 + 68q + 14t)
B(F(W) Φ X, e).
```

The equality is for literal primitive transitions, not grouped macro moves. It certifies no intermediate halt and is uniform over all p,k,q,t and all such X. Its finite output prefix is **exactly two bits longer** than the input prefix: each token P and Q has the same bit width as F(P) and F(Q), while `|Φ|=|Z AA|+2`. The strict-growth fact is a consequence of the proven source reset theorem and run-block width accounting, not a claim about the unbounded blank tape size.

The precise Lean closed cost is `6 + 68 * data.length + 14 * atCountT data + 68 * W.length + 14 * fmCountQ W`; because `data.length=q+1` and `W.length=p+k`, this simplifies to the displayed formula.

## Exact two-stack proof

The key is a **last-in-first-out right-stack code**. Define `J=(1,2)`, `u=(4,3)`, `s=(5,3)`, `C=(2,1)`, `d=(2,0)`; parentheses are 1-run and 0-run counts.

* The **first** P token consumes in 36 primitive steps and deposits right `u d`; the first Q consumes in 46 and deposits `u C e`. Both are source-certified `atc_consume_e` and `atc_preconsume`.
* Every subsequent P consumes in 36 steps, changing `u R` to `u s R`; every subsequent Q consumes in 46, changing `u R` to `u C u R`. The source-certified `atc_consume_u` and `atc_preconsume` hold for **arbitrary run-aligned R**. Their arbitrary-length induction is `fmConsumeRest`.
* The separately kernel-checked **C-free arbitrary-carry parser** `atg_staged` converts `B(Z AA X,u R)` to `B(J Φ X,A R)` at exact cost `11+68(q+1)+14t`. It relies on eight generic scanner/decoder rules, plus new source-guarded `u` terminal and marker junction lemmas.
* Saved right markers decode in reverse. `J/(A s R)→J P/(A R)` costs 32, and `J/(A C u R)→J AAAT/(A R)` costs 36. The **arbitrary list** induction `fmDecodeRest` proves that all saved markers are decoded without reordering the original W.
* The oldest base marker `d` or `C e` is discharged in 27 or 31 transitions, respectively, returning to right `e`. Hence the first marker costs **five fewer decoding steps** than an interior marker, regardless of its kind.

The source/decode contribution from all prefix tokens is `68p+82k−5`. Add the scanner/decoder `11+68(q+1)+14t` to get `68p+82k+74+68q+14t`.

Proof files:
- [ATCarryCore.lean](ATCarryCore.lean): literal source-certified generic one-token rules and right stacks.
- [ATGeneralParser.lean](ATGeneralParser.lean): independently proved unbounded C-free data parser, with no hard-coded C suffix; CI [46083147039](https://github.com/FlareZ123/bb6/actions/runs/46083147039).
- [ATFreeMonoidCore.lean](ATFreeMonoidCore.lean): universally quantified exact `fmConsumeRest` and `fmDecodeRest` list inductions, no `sorryAx`; CI [46083811592](https://github.com/FlareZ123/bb6/actions/runs/46083811592).
- [ATFreeMonoid.lean](ATFreeMonoid.lean): exact `fmSourceHead`, `fmDecodeHead`, `fmConsumeWord`, `fmDecodeWord`, `fmFullFamily`, `fmCostFormula`, and `fmFullFamilyClosed`; CI [46083890068](https://github.com/FlareZ123/bb6/actions/runs/46083890068) (all only `propext, Quot.sound`).
- [ATFreeMonoidGrowth.lean](ATFreeMonoidGrowth.lean): explicit finite bitword encoding and `fmStrictBitGrowth` (+2), with source normal form `fmFullFamilyBits` (check CI status before citing as kernel accepted).

## Significance and next obstacle

This consolidates the earlier q-unbounded `TAT ZAA` theorem, the leading P-counter rule, and the empirically discovered two-independent-counter rule. It additionally covers **arbitrary interspersed P/Q prefix words**, including words like `PPQPP`, `PPPPPQPPP`, and `P⁸ Q PP Q P`, which arise in early authentic F197 reset simulations. For perspective, an exhaustive exact macro check of **29,640** mixed words of length up to seven, all binary data lists of length up to four, and suffixes `e,Ae,Je,Ce` agreed with the formula before Lean proof; these experiments are supporting sanity checks, not the basis of the theorem.

The dominant unresolved BB(6) obligation remains a genuine **blank-orbit closed grammar**. Many authentic resets contain J/U/C markers or paired source packets with non-AA terminal suffixes. A formally established positive-growth rule is insufficient unless every genuine reset configuration is proved to have a covered safe successor. Do **not** equate prefix growth on this conditional domain with complete F197 nonhalting.
