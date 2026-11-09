# Eleven neutral radix-81 symbols for original Cryptids #623

**Agent 49, 9 November 2026.** This intermediate theorem strengthens the [third neutral ninefold theorem](ThirdNinefold.md) and Agent 8's earlier two-symbol source-certified family. It gives a substantially larger exact family of original-source B-drain successes and failures. All prepared high-level states remain synthetic; no blank-origin nonhalting theorem or exact BB(6) value follows.

## Two genuinely new four-digit contractions

For the original complete `drainB`, including all `none` cases, the two additional source equations are

```text
B(a,81*b+30,d) = B(a,b,d+240*b+96).
B(a,81*b+48,d) = B(a,b,d+240*b+152).
```

They hold for **every** `a,b,d∈ℕ`, including `a=0` and `b=0`. The first follows by four unconditional/positive first-counter reductions of residues `0,0,2,1`: before the first negative-counter branch the zero residue has raised the counter twice, so there is no zero exception. The second follows by residues `0,0,1,1`. Exact arithmetic (including all third-counter shifts) is proved in [Eleven81Source.lean](Eleven81Source.lean). The unmodified-source Lean CI [42573413415](https://github.com/FlareZ123/bb6/actions/runs/42573413415) passed both proofs with standard foundational axioms only.

The nine two-symbol compositions of the already source-verified residues `{0,6,8}` are distinct modulo `81`, and neither 30 nor 48 occurs among them. Hence there are **eleven** exact neutral residue choices.

## All eleven complete transitions

For any `b>0`, each row gives an *exact equality* between full original drains for every `a,d`, with a common first-counter input:

```text
B(a,81*b+r,d) = B(a,b,d+240*b+3*r+c_r).
```

| Residue `r` | Charge `c_r` | Third-counter increment beyond `240*b` |
| ---: | ---: | ---: |
| 0 | 4 | 4 |
| 6 | 6 | 24 |
| 8 | 4 | 28 |
| 30 | 6 | 96 |
| 48 | 8 | 152 |
| 54 | 6 | 168 |
| 60 | 8 | 188 |
| 62 | 6 | 192 |
| 72 | 4 | 220 |
| 78 | 6 | 240 |
| 80 | 4 | 244 |

The nine compositional cases follow by two applications of the ninefold source identities. The two primitive cases are the proofs above. Source theorem `drain81_step` in [Eleven81FamilySource.lean](Eleven81FamilySource.lean) covers the complete table without finite input limitations.

## Eleven-letter injection and full output

Let `R` be the eleven-element alphabet from the table, and for each word `w` define

```text
P([])=6,             P(r::w)=81*P(w)+r,
Q([])=4,             Q(r::w)=Q(w)+c_r.
```

For all natural first counters `a` and third counters `d`, the original complete drain is

```text
B(a,P(w),d) = some D(a,d+3*P(w)+Q(w)).
```

Every `P(w)` is positive and even. For distinct words, `P(w)` is different, because residues modulo 81 distinguish their leading symbols, and the positive base `P([])=6` cannot coincide with a nonempty word. These facts are the all-word source theorems `block81_drain` and `block81_injective`.

Therefore each word length `n` provides **exactly `11^n` distinct explicitly successful block counts**, as opposed to `9^n` given by the earlier three residues at the same radix-81 depth. The lower-bound growth exponent of the constructed regular language is `log(11)/log(81)≈0.54566458`; the prior three-residue language gave exactly `1/2`. This is only a lower bound on the supply of successful synthetic B inputs, and does not measure genuine blank-root visitation.

Any such `P(w)` also supplies a prepared two-return escape by the unchanged high-level machine:

```text
T(T(D(P(w),P(w)-2))) = some D(2+3*P(w)+Q(w),7).
```

The existing original branch derivation for even positive block counts applies verbatim. Proving reachability of one of these states from the blank root remains open.

## Broader candidate and root-sensitive relevance

A finite exact symbolic scan of residues `r<3^(2n)` suggested that the *maximal* number `N_n` of universally first-counter-preserving, exact-translation residues may equal

```text
N_n = Σ_(j=0)^n 2^j * Catalan(j).
```

The observed counts for `n=1,2,3,4,5,6` were `3,11,51,275,1619,10067`. These are **experimental**; no all-depth completeness proof or exact Catalan bijection has been established. In particular, the eleven residue theorem proves the `n=2` set **exists** but does not establish maximality.

A 10,000-section-state exact integer scan of the actual `D(0,7)` orbit found that **1,312** original B-drain arguments admitted at least one radix-81 neutral prefix, of which 169 admitted two or more and 24 admitted three. This is finite diagnostic data. It demonstrates applicability to genuine orbit inputs but is not an orbit invariant or a halting decision.

## Reproducibility and status

The [source module](Eleven81FamilySource.lean) imports the pinned original-machine pathway through [Eleven81Source.lean](Eleven81Source.lean) and [ThirdNinefoldSource.lean](ThirdNinefoldSource.lean). All eleven residue equations and word injection compile in Lean 4.36.0-rc2 against the exact source recurrence interface; the stronger original-Cryptids imported CI job is [42574126182](https://github.com/FlareZ123/bb6/actions/runs/42574126182). Update its verdict when complete.

The decisive BB(6) barrier remains finding an all-time blank-root inductive certificate or an actual terminating return. The current source identities give a lossless renormalization usable in such a future proof, but no such proof is presently known.
