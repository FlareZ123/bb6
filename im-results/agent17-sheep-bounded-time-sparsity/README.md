# Quantitative finite-time sparsity of Sheep halting starts

**Status, 9 November 2026:** a self-contained mathematical theorem about **all positive even Sheep section starting integers**, proved below from the exact published first-even return. It gives a uniform upper bound for any return horizon and a density-zero conclusion for a horizon increasing as a constant times the square root of the starting size's bit length. It is **not a statement about the eventual fate of the particular blank-tape entry 10** and does not determine BB(6). No Lean kernel theorem or external novelty review is claimed. Keep this result in `im-results/`.

## Definition and precise counting theorem

For every even section state `x>=10`, factor `x=2^a u`, `a>=1`, `u` odd. The Sheep section halts if `u=1`. At every other such state its genuine nonterminal successor is

```
 F(x) = x+a+3                if u=3,
 F(x) = x+a+(u-1)/2          if u>=5.
```

Factor `F(x)-1=2^h q` with odd `q>=1`. The exact first-even return is `E(x)=1+3^h q`. Original six-state source authenticity, strict increase, and the all-time equivalence of original-machine halting with reaching a power of two from the genuine blank section entry `10` are already in [Agent16's source bridge](../agent16-sheep-even-return/README.md), [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). Here `x` is allowed to be any even positive legal section state, rather than necessarily blank-reachable.

Fix `N>=10` and any integer `n>=0`. Let `H(N,n)` be the number of even integers `x` in `[10,N]` whose deterministic first-even path first encounters a power of two in **at most n successful E returns**. Put

[
\alpha=\log_2 3,\qquad L=\lceil\log_2 N\rceil+6.
]

**Uniform theorem:**

[
\boxed{H(N,n)\ \le\ 2(n+1)\,9^n\,
\alpha^{\,n^2+2n}\, L^{\,2n+1}.}
\tag{1}
]

No asymptotic or search horizon is hidden in (1). In particular, for any fixed real `0<c<1/sqrt(log_2(log_2 3))`, taking

[
n(N)=\left\lfloor c\sqrt{\log_2 N}\right\rfloor
]

yields the rigorous density bound

[
\boxed{H(N,n(N))\ \le\
N^{\,c^2\log_2(\log_2 3)+o(1)}=o(N).}
\tag{2}
]

Here `log_2(log_2 3)≈0.66444870745` and the upper permissible constant is approximately `1.22678729470`. For instance `c=1` establishes that asymptotically almost every positive even source `x<=N` avoids a terminal power for at least `floor(sqrt(log_2 N))` successful first-even returns. This is a *growing-horizon finite-time statement* about varying initial states. It neither proves that any individual state runs forever nor supplies a density estimate for eventual halting at unbounded time.

## Proof

**1. Sharp universal return-growth exponent.** For all legal nonterminal even `x>=10`, the factorization `x=2^a u` gives `F(x)<=2x`. In the generic case `a<=x/2` (because `a<=2^(a-1)u`) and `(u-1)/2<=x/2`; for `u=3`, `a+3<=3*2^a=x`.

Let `z=F(x)-1=2^h q`, with `q>=1`. Since `3^h=(2^h)^alpha` and `q<=q^alpha`,
[
E(x)-1=3^h q\le (2^h q)^\alpha=z^\alpha\le(2x)^\alpha.
]
Since `x>=10` and `alpha>1`, `1+(2x)^alpha <=(4x)^alpha`. Therefore
[
\boxed{E(x)\le (4x)^\alpha.}\tag{3}
]

The exponent `alpha` is *asymptotically optimal for a pointwise polynomial upper bound*: for `h=4m+1>=5`, `u=(2^(h+1)+1)/5` is an odd integer at least 13, because `2^(h+1)=4 (mod 5)` and the quotient is odd. Taking `x_h=2u` gives `F(x_h)-1=2^h`, hence `E(x_h)=1+3^h` and
[
\lim_{m\to\infty}\frac{\log E(x_{4m+1})}{\log x_{4m+1}}=\log_2 3.
]
The optimality claim concerns only the exponent of this universal *one-return growth* bound, without asserting tightness of the counting estimate.

**2. All intermediate sizes from a small initial state.** Suppose a legal orbit `x_0,...,x_k` has `x_0<=N`, and write `b_i=log_2 x_i`. From (3),
[
b_{i+1}\le\alpha(b_i+2).
]
Let `C=2alpha/(alpha-1)<6`. Then
[
b_{i+1}+C\le\alpha(b_i+C),
]
so by induction `b_i+C<=alpha^i(log_2 N+C)`. Since `L=ceil(log_2 N)+6`, we have
[
\boxed{\log_2 x_i\le\alpha^i L.}\tag{4}
]
Define the integer `J_i=ceil(alpha^i L)`. Every intermediate state is at most `2^(J_i)`, and a terminal power `2^j` reached at return `k` has `j<=J_k`.

**3. Direct inverse-branch bound valid for *every* even target.** Fix even `y>=10` with `y<=2^J`. Any legal parent `x` satisfying `E(x)=y` obeys `x<y` by the existing strict-increase theorem and thus `a=v2(x)<=J`. Also `F(x)<=E(x)=y`: for `F(x)-1=2^h q`, this is `1+2^h q<=1+3^h q`. Consequently `0<=h<=J`.

For generic sources `u>=5`, the exact algebraic identity is
[
\boxed{2(F(x)-1)=(2^{a+1}+1)u+2a-3.}\tag{5}
]
For fixed `y,a,h`, the value `q=(y-1)/3^h` (if integral) fixes `F(x)=1+2^h q`. Since `2^{a+1}+1>0`, equation (5) determines *at most one* `u`, hence at most one source `x`. There are at most `J(J+1)` generic `(a,h)` pairs. Exceptional sources `u=3` are each exactly `x=3*2^a` and contribute at most `J` extra candidates. Therefore
[
\boxed{\#\{x\ge10:E(x)=y\}\le J(J+2)\le(J+1)^2.}\tag{6}
]
This bound includes exceptional section starts and does not silently discard alternate inverse branches.

**4. Count each terminating time backwards.** For an orbit of exactly `k` returns, the terminal power `x_k` has at most `J_k` possible exponent values. Its parent `x_{k-1}`, with `x_k<=2^(J_k)`, has at most `(J_k+1)^2` choices by (6). Repeating the bound at level `i` for each `x_i<=2^(J_i)` gives
[
\#\{x_0\le N:\text{first terminal power at step }k\}
\le J_k\prod_{i=1}^k (J_i+1)^2.\tag{7}
]
Since `L>=2`, `alpha>1`, `J_i<=2alpha^i L`, and `J_i+1<=3alpha^i L`,
[
J_k\prod_{i=1}^k(J_i+1)^2
\le 2\cdot 9^k\cdot
\alpha^{\,k+2\sum_{i=1}^k i}L^{2k+1}
=2\cdot9^k\alpha^{\,k^2+2k}L^{2k+1}.\tag{8}
]
The right-hand side increases with `k>=0`. Summing over `k=0,...,n` yields (1). There is no possibility of a single starting `x_0` being counted at two distinct first halting indices, because the deterministic map is undefined once the terminal power is reached.

**5. Density at a growing horizon.** With `n=floor(c sqrt(log_2 N))` and `L=O(log N)`, taking base-two logarithms of (1) gives
[
\log_2 H(N,n)\le
n^2\log_2\alpha+O(n\log\log N+\log\log N)
=c^2\log_2\alpha\,\log_2 N+
O(\sqrt{\log N}\log\log N).
]
The exponent of `N` is strictly less than one for `c<1/sqrt(log_2 alpha)`, proving (2).

## Scientific boundary and next use

The bound is **proof-based, all-N, all-n**, with no numerical simulation premise. It counts potential initial even section states, and the argument stays valid whether a given candidate path reaches the terminal power or not. The arithmetic exponent `log_2 3` is sharp for one-step growth, but the inverse-branch product is coarse; improved constraints on *actual histories* could sharpen (1).

The result has no implication that the single integer `10` is outside the counted set. It cannot decide the Sheep machine and cannot be promoted to `results/` as a BB(6) breakthrough. To advance BB(6), one must find an authentic blank-root invariant or complete all-exponent source exclusion of reachable halting powers; an average-case rarity statement alone is insufficient.
