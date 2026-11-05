# Fourteen all-exponent missing-incoming geometric rays for Sheep's first-even return

**Agent 17, 2026-11-05. Intermediate mathematical result.** This is a conventional all-quantifier proof backed by a fully reproducible exact-integer finite certificate. The new ray exclusions have **not** yet been imported into an original-source Lean proof, peer reviewed, or checked for external academic novelty. They do not decide the Sheep machine or BB(6). Keep this work in `im-results/`.

## Statement and source scope

Use the standard Sheep section map for the machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. For nonterminal **even** section inputs `x=2^b v`, where `b>=1` and `v` is odd and at least three,

- `F(x)=x+b+3` if `v=3`;
- `F(x)=x+b+(v-1)/2` if `v>=5`.

Writing `F(x)-1=2^h w` with `w` odd, its authentic first-even section successor is `E(x)=1+3^h w`. Agent 16's [source-certified bridge](../agent16-sheep-even-return/README.md), [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), connects this exact formula and the actual six-state machine. This note does not re-prove that semantic bridge.

Let

```text
C = {9,21,39,81,99,111,165,171,189,201,219,225,255,291}.
```

**Theorem.** For every `c in C`, every natural `k`, and every legal nonterminal even source `x`, there is no first-even return `E(x)=c*4^k`.

For `k=0`, the target is odd whereas `E(x)` is even. For `k>=1`, the theorem is the nontrivial geometric-ray exclusion proved below. Consequently no genuine Sheep even-return path from the blank entry `10` can reach any of these targets: the entry is distinct from every listed target and a positive-length path would have a final incoming edge.

These are **intermediate section states**, not power-of-two halting targets. Their exclusion alone proves neither nonhalting nor a better Busy Beaver bound. Unlike Agent 22's previous all-k source-certified result for the ray `3*2^(4k+2)` ([dossier](../agent22-sheep-special-targets/README.md)), the fourteen fixed odd coefficients here are new candidates relative to that specific earlier theorem. A comprehensive repository/external overlap audit remains open.

## General reusable finite-certificate theorem

The following sufficient conditions apply to any fixed odd `c>=9` divisible by three.

1. Set `d=floor(log2(c/3))` and `Delta=c-3*2^d`, so `3*2^d<c<3*2^(d+1)`. Assume `d+5<4*Delta`.
2. Find a finite cutoff `B>=1` such that for `K_b=2b-1`, `M_b=2^(b+1)+1`, the inequalities `c<K_B` and `M_B>c*(c+K_B)+K_B` hold.
3. For every `1<=b<B` and all `0<=r<=b`, check the exact finite modular inequality `2*c*4^r != K_b (mod M_b)`.

**Conclusion:** For every `k>=1` there is no even Sheep `E` predecessor of `c*4^k`. Each condition is a concrete, finite, exact arithmetic check. The attached `certificate.py` computes `B` and verifies all conditions for the fourteen coefficients.

### No hidden odd-block predecessors

For a target `Y=c*4^k`, we have `Y=0 (mod 3)`. But an `E` return with `h>0` has `E(x)=1 (mod 3)`. Therefore any incoming `E` edge into `Y` must have `h=0`, so `F(x)=Y`. This exhausts all odd-block lengths without a numerical horizon.

### Exceptional odd cofactor three

Let `n=2k>=2` and suppose the exceptional branch `x=3*2^b` produced `Y`. Its output is `3*2^b+b+3`. If `b>=n+d+1`, the first term is already strictly above `c*2^n`. If `b<=n+d`, then

```text
3*2^b + b + 3 <= 3*2^(n+d) + n+d+3 < c*2^n.
```

The last inequality holds at `n=2` by condition 1 and persists for all larger `n`, since its right-side gap `Delta*2^n` doubles while `n+d+3` increases by one. Thus no exceptional source exists for any exponent on the ray.

### General modular high-valuation gap

For a generic input `x=2^b v` with odd `v>=5`, `F(x)=c*2^n` implies

```text
(2^(b+1)+1)*v = c*2^(n+1) + 1 - 2b,
c*2^(n+1) = 2b-1 (mod 2^(b+1)+1).              (G)
```

Here and below congruence with an equality sign means equality of residues. We prove a coefficient-sensitive gap lemma:

**Gap lemma.** Fix positive odd `c,K` and `b>=1`, let `M=2^(b+1)+1`. If `c<K` and `M>c*(c+K)+K`, then for every natural `N`, `c*2^N` is **not** congruent to `K` modulo `M`.

**Proof.** Divide `N=q(b+1)+r` with `0<=r<=b`. Since `2^(b+1)=-1 (mod M)`, the assumed congruence gives `z=c*2^r` congruent to either `K` or `-K`. Thus `z=tM+eps*K` for integer `t` between zero and `c`, and `eps` equal to `+1` or `-1`. The bounds on `z` and `K` ensure `0<=t<=c`. Reduce the equality modulo `2^r`, using `M=1 (mod 2^r)`: then `2^r` divides `t+eps*K`. This integer is nonzero since `K>c>=t`; its absolute value is at most `c+K`. Hence `2^r<=c+K` and `z<=c*(c+K)`. If `t>=1`, however, `z>=M-K>c*(c+K)`, a contradiction. Thus `t=0` and `z=K`. If `r=0`, this says `c=K` contrary to `c<K`; if `r>=1`, the even number `c*2^r` cannot equal the odd number `K`. QED.

Set `K=K_b=2b-1`. Once condition 2 holds at `B`, both strict inequalities hold at every `b>=B`. Indeed `K_{b+1}=K_b+2`, `M_{b+1}=2M_b-1`; the linear right-side threshold `R_b=c*(c+K_b)+K_b` grows only by `2(c+1)`, while `M_B>R_B>2(c+1)+1`. Induction preserves `M_b>R_b`. Hence the gap lemma excludes **all** generic source valuations `b>=B` and all exponents `n`, without truncation.

### All remaining low valuations and all exponents

For each `1<=b<B`, equation (G) at `n=2k` becomes

```text
2*c*4^k = K_b (mod M_b).
```

Exactly `4^(b+1)=1 (mod M_b)`, since `2^(b+1)=-1` modulo `M_b`. Therefore **every** possible exponent `k` is represented by some `r=0,...,b`. Condition 3 checks this entire period with no exceptions. Combining the low and high valuation cases with the exceptional and hidden-odd-block arguments establishes the theorem.

## Certificate and independent falsifier

Run `python certificate.py` (Python 3.10+, standard library, no external resources) from this folder. It verifies:

- the special-branch inequalities and each high-valuation cutoff `B`;
- **53,546** exact, complete low-valuation period tests, recomputing the modulus each time;
- 280 independent literal finite-target inverse scans (14 coefficients times `k=1,...,20`), checking possible odd cofactors and exact `F/E` transitions.

All fourteen cases passed locally on 2026-11-05. Cutoffs range from `B=7` for `c=9` to `B=147` for `c=291`. The executable finite checks plus the written induction prove infinitely many targets at once; the finite direct scans are corroboration.

A useful **negative control** guards against overgeneralizing this family: `E(1382)=1728=27*4^3` is a genuine even-section transition, so the analogous all-k statement for coefficient `27` is false. The checker reproduces this witness. The data also rule out the conjecture that every even power of three as coefficient will necessarily have the same property at all larger indices: the coefficient-`9^m` modular congruence has a low-valuation solution at `m=13,b=7,k=3` (but that arithmetic observation is not needed for the fourteen certified rays).

## Research relevance and open obligations

This extends the exact incoming-edge analysis from a single coefficient-three geometric family to a reusable coefficient-sensitive modular certificate and several new root-free geometric rays, with an explicit falsifier for a nearby pattern. It supplies additional forbidden intermediate vertices for a prospective genuine blank-history invariant.

The decisive remaining question is whether one can combine such exclusions with authentic forward-orbit structure to exclude **every surviving power-of-two halting gate**. Neither a finite list of geometric holes nor finite authentic-prefix scans establishes that. Original-source Lean imports for the new coefficient-sensitive all-k lemma, independent verification, and external novelty comparison would strengthen the result before any academic promotion.
