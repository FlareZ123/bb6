# An infinite genuine-witness Sheep quotient path with no ordinary integer realization

**Agent 40, 7 November 2026. Intermediate constructive mathematical counterexample.** For **every even modulus divisible by 16**, the generic Sheep first-even quotient graph contains a legitimate self-loop at the residue **−2 modulo m**. Every finite repetition of this loop is realized by consecutive genuine generic first-even returns of a single positive integer, yet **no positive integer** follows that infinite constant-residue path. For m=16 this is the concrete residue **14**, with the same sharp obstruction.

This explicit failure of infinite-path lifting clarifies the exact boundary of the [all-even-modulus finite-path theorem](MIXED-FINITE-PATH-LIFTING.md). Every finite quotient path is genuinely physically concatenable from a freely chosen positive integer, but compatible finite starts can converge to a negative 2-adic integer and have no ordinary positive-integer limit. This has **no inference** about the original Sheep blank-start even state **10**, and does not decide its halting behavior or BB(6).

## One-step forced generic branch

For every positive even section integer x satisfying `x==14 (mod 16)`, write `x=16k-2` with k>=1, so its exact 2-adic valuation is a=1 and odd part u=x/2=8k−1>=7. The published **generic** Sheep section formula is

```
F(x)=x+1+(u-1)/2=(5x+2)/4=20k-2,
```

which is already even. Hence the **genuine first-even return is exactly** `E(x)=F(x)` with odd-block length h=0 and all cofactor guards valid. In particular,

```
4*(E(x)+2)=5*(x+2).                              (1)
```

The congruence x=14 mod16 forces (1), with no finite simulation hypothesis. Conversely, for a positive x in this residue, its genuine return must be (1), and there is no exceptional odd-part-three source (the only a=1 exceptional source is x=6).

### Every finite constant-14 walk is genuinely realizable

For any N>=0, choose

`x_0 = 2^(2N+4)-2`.

For each i=0,...,N, define

`x_i=5^i * 2^(2(N-i)+4)-2.`

Every x_i is positive and `x_i ≡14 (mod16)`; its odd part is >=7. For i<N, direct algebra gives

`4*(x_(i+1)+2)=5*(x_i+2)`.

The identity (1) forces `E(x_i)=x_(i+1)` **on the actual deterministic generic integer section**, so one starting integer x0 follows N consecutive genuine generic first-even returns, all at residue14 mod16. Because x_N+2=16*5^N, the next genuine return has `E(x_N)+2=20*5^N`, exactly divisible by four but **not** by sixteen. Thus that particular finite witness exits residue14 at its next step. The family covers arbitrarily long prefixes N; no single initial integer works for all N.

This is a literal physical-integer section trajectory. The earlier machine-source bridge verifies the published section semantics when used for authentic states, but the arbitrary constructed starts here are not claimed to be genuine blank-tape reachable.

### Generalization to every modulus divisible by 16

Let `m=2^p*q` with p>=4 and q odd. Write `r=m−2`, representing the full residue `−2 modm`. The source `x=4m−2` is positive, congruent to `r`, and congruent to 14 modulo16. Its **genuine** generic first-even return obeys `E(x)+2=5m`, so `E(x)≡r modm`. Thus `r->r` is a legal self-loop of the original **generic** quotient `G_m`.

For **every N>=0**, choose the positive integer

`x_0=4^N*m−2`, and define `x_i=5^i*4^(N−i)*m−2` for `0<=i<=N`.

Each `x_i` is positive and congruent to r modulo m (hence 14 modulo16). For each i<N, the forced identity (1) gives `E(x_i)=x_(i+1)` with a=1,h=0 and legal generic odd cofactors. The chosen single integer `x_0` therefore realizes the full N-edge self-loop. Its next return from `x_N` leaves the target residue because `v2(x_N+2)=v2(m)=p` drops to `p−2`, so `x_(N+1)+2` is no longer divisible by m.

For a hypothetical positive integer that realized the infinite r self-loop, all its consecutive orbit states would also be 14 modulo16; the no-infinite-14 proof below already contradicts this. Thus **the same explicit failure of infinite lifting occurs for every m with 16 dividing m**, including arbitrary odd factors q and arbitrarily large dyadic precision p. The initial starts `4^N m−2` converge 2-adically to −2 as N grows.

[verify_noncompact_all.py](verify_noncompact_all.py) independently checks **2,800 literal generic single-integer self-loop prefixes** with N=0..39, p=4..10 and q in {1,3,5,7,9,11,15,21,25,35}, including exact forced steps and exit. The all-m proof is elementary and independent of that finite check.

### No positive integer follows the infinite constant-14 path

Suppose some positive integer x0 has an infinite first-even section trajectory all at residue14 mod16. Every one-step transition must satisfy (1). By ordinary induction,

`4^n * (x_n+2) = 5^n * (x_0+2)` for every n.

Since 4 and 5 are coprime, Euclid's lemma implies

`4^n | (x_0+2)` for every n.

The positive fixed natural integer `x_0+2` cannot be divisible by arbitrarily large powers of four, a contradiction. This excludes the infinite constant-14 quotient path for **every** positive integer source, including starts chosen without any generic-a-priori assumptions. The residue14 forces generic a=1,h=0 at each hypothetical step, so the proof is exhaustive.

For a direct quantitative statement, put `b=v2(x0+2)>=4`. While the orbit remains 14 mod16, (1) forces its valuation to fall by exactly two each return. The maximal number of initial consecutive **vertices** with residue14 is

`1+floor((b-4)/2)`,

and the next physical return necessarily exits that residue. The bound depends on the full starting integer's unbounded 2-adic precision, which a fixed quotient mod16 cannot record.

## 2-adic interpretation and formal evidence

As N increases, `x_0(N)=2^(2N+4)-2` converges **2-adically to −2**, an integer outside the allowed positive initial section states. The formal fixed point of (1) is x=−2, since `E(x)+2=(5/4)*(x+2)`; the factor 1/4 is interpreted only on the relevant decreasing domains of divisibility, and this is a heuristic geometric explanation rather than a claim that the original Turing machine has a genuine 2-adic execution. The necessary powers-of-four divisibility argument above is elementary in the ordinary natural numbers.

The complete independent standalone [Lean kernel certificate](SheepNoncompactLean.lean) compiles under Lean 4.36.0-rc2 with only `[propext, Quot.sound]`, no `sorryAx`. Its theorem `forced_identity` establishes (1) for any x with 16 dividing x+2. Its theorem `orbit_identity` proves `4^n*(orbit x n+2)=5^n*(x+2)` under the *all-time residue14* hypothesis, where `forced x=(5*x+2)/4`. Finally **`no_positive_infinite_selfloop`** proves that no natural x can satisfy `∀n,16|(orbit x n+2)`; this uses coprimality `4^n ⟂ 5^n` and growth `n<4^n` in the Lean kernel. This is an arithmetic model of the forced section branch, linked to the published exact Sheep formula by the paper derivation, **not** a new source-importing Lean statement about the original machine.

[verify_noncompact.py](verify_noncompact.py) independently checked all literal actual generic first-even trajectories with N=0,...,100, including cofactor bounds, every finite 14-residue step, exact values `x_i+2=5^i 2^(2(N-i)+4)`, and the next-step exit to residue2 mod16. These 101 finite trajectories corroborate the universal argument without replacing it.

**Research limit:** This every-m-divisible-by-16 family proves a uniform, explicit gap between arbitrary finite genuine-path realizability and existence of a single genuine *infinite* positive-integer path. It is a methodological constraint on finite quotient proof strategies, not evidence that Sheep halts or fails to halt from 10. The exact value BB(6) remains unsolved. The new result belongs in `im-results/` pending source-level integration and external novelty assessment.
