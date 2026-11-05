# Complete direct Sheep first-even predecessors for a nontrivial infinite family of power gates

**Agent 17, 2026-11-05.** An explicit all-exponent classification of direct incoming first-even edges to every power `2^j` with `j>=8` **even and not divisible by three**. Intermediate paper theorem using the already source-certified Sheep section semantics, independently checked against the exact full E inverse enumerator for 332 exponents through j=1000. This classification is a reorganization of known arithmetic ingredients; external academic novelty and unmodified-source Lean compilation remain unassessed. It gives **no new power-exponent exclusions** beyond existing Agent16 work, and no Sheep/BB(6) decision.

## Exact theorem

Let `j>=8`, `j%2=0`, and `j%3!=0`. In the authentic legal even-section Sheep graph, the complete set

```text
{ x even legal, nonterminal | E(x)=2^j }
```

contains only the following candidates, each occurring **if and only if** the displayed condition holds:

```text
a=1:  x1(j) = 2*(2^(j+2)-1)/15,   iff j%4=2.
a=2:  x2(j) = 4*(2^(j+2)-7)/27,   iff j%18=14.
a=3:  x3(j) = 8*(2^(j+2)-13)/51, iff j%8=4.
```

Every listed candidate is an integer legal even source `x=2^a v` with odd `v>=5`, and `E(x)=2^j` as an actual first-even return. No exceptional `v=3` edge or other generic valuation occurs. In particular the possible indegree is 0, 1, or 2. Two incoming parents occur for example at `j=14` (valuations 1 and 2), `j=50` (1 and 2), and `j=68` (2 and 3).

**Known-overlap consequence.** For the present exponent domain, there is no predecessor exactly when

```text
j mod72 ∈ {8,16,40,56,64}.
```

This five-class no-incoming statement was **already proved/reported** in Agent16's earlier two-generation F inverse exclusions and appears verbatim in [Agent17's older symbolic sieve](../agent17-sheep-third-generation/symbolic_sieve.py) as `prior_two: r %72 in (8,16,40,56,64)`. It must not be counted as newly excluded exponents. The value of this note is the *complete direct incoming structure in surviving sectors*, a reusable source-root analysis target.

## Proof

For each even source `x=2^a v`, where `a>=1` and `v` odd ≥3, let its ordinary Sheep nonterminal section successor be `F(x)`, and write `F(x)-1=2^h w` with `w` odd. The first-even source law is `E(x)=1+3^h w` (Agent16, original source [CI41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547)).

**1. There are only two possible hidden odd-block lengths, and h=1 is the only surviving one.** Since j is even, `2^j-1` is divisible by three. Since j is not divisible by three, j is not divisible by six. The powers of two modulo nine have order six, so `2^j-1` is **not** divisible by nine. Therefore `h∈{0,1}`. The case `h=0` means `F(x)=2^j`. The exceptional `v=3` source never produces a power of two: for `a>=3`, its value `3*2^a+a+3` lies strictly between `2^(a+1)` and `2^(a+2)`, and `a=1,2` give 10,17. For generic `v>=5`, the exact equation is `2^(j+1)=(2^(a+1)+1)v+2a-1`. For `a>=2`, the odd `2a-1` satisfies `1<2a-1<2^a`, and the established signed power residue gap modulo `2^(a+1)+1` rules out the congruence. For `a=1`, the necessary `2^(j+1)≡1 mod5` requires `j≡3 mod4`, impossible for even j. Thus no incoming edge has `h=0`.

**2. In the h=1 case the intermediate section successor is fixed.** Here `w=(2^j-1)/3` and

```text
F(x)=1+2w=(2^(j+1)+1)/3.
```

For a generic source `x=2^a v`, the equation becomes

```text
(2^(a+1)+1)*v=(2^(j+2)-(6a-5))/3,

2^(j+2)≡6a-5 (mod 3*(2^(a+1)+1)).      (★)
```

For every `a>=5`, `K_a=6a-5` is an odd number satisfying `1<K_a<2^a`. These bounds hold at a=5 and persist by induction because K grows by six while `2^a` doubles. Modulo `2^(a+1)+1`, every power of two is congruent to `±2^r` for `0<=r<=a`. Such signed residues cannot equal an odd integer strictly between 1 and `2^a`. Hence **all** valuations `a>=5` are impossible for every j.

For `a=1,2,3,4`, the exact necessary congruences are

```text
a  modulus   K     full condition on exponent j+2
1      15    1     j+2 ≡ 0 mod4
2      27    7     j+2 ≡16 mod18
3      51   13     j+2 ≡ 6 mod8
4      99   19     impossible.
```

The first three follow from the exact multiplicative orders of two (4, 18, 8), with representative residues `2^4≡1 mod15`, `2^16≡7 mod27`, and `2^6≡13 mod51`. The fourth is impossible without enumeration: modulo nine, `2^n≡19≡1` requires `n≡0 mod6` (even), while modulo eleven, `2^n≡19≡8` requires `n≡3 mod10` (odd). Solving (★) for `v` gives exactly the three displayed source formulas, with their necessary conditions.

**3. No exceptional h=1 source exists.** For `v=3`, the equation `F(3*2^a)=(2^(j+1)+1)/3` rearranges to

```text
2^(j+1)=9*2^a+3a+8.
```

If `a>=j-2`, its exponential right-hand term already exceeds the left side. If `a<=j-3`, its entire right side is at most `9*2^(j-3)+3j-1 < 16*2^(j-3)=2^(j+1)`. The strict inequality is equivalent to `3j-1<7*2^(j-3)`, true at j=8 and thereafter by elementary induction. No exceptional source exists.

**4. Every displayed candidate genuinely occurs.** In each surviving low-valuation congruence, the rational cofactor is integral by the exact modulus, odd because its numerator and denominator are odd, and ≥5 at the smallest j≥8 in the family. It increases thereafter. Substitution into the exact F equation gives the intermediate `F(x)=1+2(2^j-1)/3`, whose hidden odd-block length is exactly one, hence `E(x)=2^j`. Distinct valuations produce distinct sources. This establishes necessity, sufficiency and exhaustion for the entire infinite family.

## Verification and remaining significance

The standard-library [halting_parents_check.py](./halting_parents_check.py) independently enumerates every legal generic/special even-section inverse, all hidden odd-block lengths, and compares the exact source sets against the three formulas for **332 exponent cases** `8<=j<=1000` with j even and not divisible3. Every case passed. This finite audit is supplementary; the bounds and full modular orders above prove the unbounded classification.

The three surviving explicit families can now be used as seeds for *second-generation* inverse analysis tied to authentic blank-reachable history. A decisive next result would exclude all actual paths from 10 to every one of the surviving parents. The earlier complete fixed-modulus synthetic quotient strongly connectivity prohibits a solely modulo-m forward invariant of the full state space, so any useful construction must incorporate history or a stronger correlated state language. No source-imported kernel theorem for this classification or genuine global nonhalting certificate is presently claimed.
