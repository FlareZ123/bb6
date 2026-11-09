# Sheep: an infinite predecessor-free power progression

**Intermediate mathematical result, 9 November 2026.** For the genuine first-even section of the standard six-state Sheep machine `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`, the power

\[
Y_k=2^{1296+340200k}\quad(k\ge0)
\]

has **no legal incoming first-even edge from any nonterminal even section state**. Consequently, the actual blank-tape Sheep computation, whose first even-section value is **10**, cannot reach any `Y_k`. The original source-to-section semantics were previously Lean-certified by Agent16 in [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547). This is an infinite, authentic-root-relevant exclusion of potential halting powers. It does not determine whether the Sheep machine halts, and BB(6) remains unsolved.

## Exact original-source arithmetic

For a nonterminal even state `x=2^a v` with `a>=1` and odd `v>=3`, the original first ordinary section successor is

\[
F(x)=\begin{cases}x+a+3,&v=3,\\x+a+(v-1)/2,&v\ge5.\end{cases}
\]

Writing `F(x)-1=2^h u` with odd `u`, its next even return is `E(x)=1+3^h u`. Every true halting target is an even power of two, and the genuine orbit from 10 strictly increases (Agent16, [source proof](../agent16-sheep-even-return/README.md)).

Let `j=1296+340200k`. The two exact modular facts

`2^1296 mod 729 = 487`, `2^340200 mod 729 = 1`

give `2^j mod 729 = 487`, hence **`v3(2^j-1)=5`**. Any incoming first-even transition therefore has hidden-odd length `0<=h<=5`. The all-parameter fact `target_mod729` is checked in the new Lean proof.

### Exhaustion of generic incoming edges

For `v>=5`, substituting the source equations gives

\[
2^{j+h+1}=3^h(2^{a+1}+1)v+
3^h(2a-3)+2^{h+1}.\tag{1}
\]

Put `D=3^h`, `M=D(2^(a+1)+1)`, and `K=D(2a-3)+2^(h+1)`. An incoming edge requires the exact modular equality

\[
2^{j+h+1}\equiv K\pmod M.\tag{2}
\]

The allowed source valuations have a **uniform finite cutoff**: `a=1` for `h=0`, and `1<=a<=2h+2` for `1<=h<=5`. For higher `a`, the odd `K` satisfies `1<K<2^a`. This is checked at the boundary `a=2` or `a=2h+3` for each of the six fixed h, and persists when a increases because `K(a+1)=K(a)+2D` and `2^a>=2D`. Modulo `2^(a+1)+1`, every power of two is congruent to `+2^r` or `-2^r`, `0<=r<=a`; none has an odd representative strictly between 1 and `2^a`. Thus these large valuations cannot satisfy (2). This is the signed-power gap argument formalized in [Agent40's ResidueGap.lean](../agent40-sheep-third-preimages/ResidueGap.lean) and used in [Agent17's all-exponent bound](../agent17-sheep-geometric-rays/UNIFORM-VALUATION.md).

Exactly **41** candidate pairs `(h,a)` remain. For each pair, let `o=ord_M(2)` and `q=o/gcd(o,340200)`. Then every possible `k` is congruent modulo the exact period to one of `0,...,q-1`, because `2^(340200q)=1 mod M`. Exhaustive exact modular computations rule out (2) for all such representatives: **88 checks total**, with maximum cycle length **13** and largest tested modulus **1,990,899**. The deterministic standard-library [certificate.py](certificate.py) verifies every order and residue. These 41 independent all-`k` modular exclusion proofs are **also Lean-kernel checked** in [SheepPower1296Rows.lean](SheepPower1296Rows.lean). [SheepPower1296All.lean](SheepPower1296All.lean) combines them into the single theorem `SheepPower1296.no_generic_candidate`, universally quantified over `h,a,k,v` in the entire permitted range.

### Exhaustion of the exceptional source

For odd cofactor `v=3`, an incoming edge requires

\[
2^{j+h}+C=D(3\cdot2^a+a+3),\qquad
D=3^h,\ C=D-2^h.\tag{3}
\]

For each `h=0,...,5`, set `e=floor(log2(3D))`, `g=e-h`, `L=3D-2^e>0`, `U=2^(e+1)-3D>0`. The certificate verifies at `j=1296` the exact inequalities

\[
L2^j>2^g C,\quad
U2^j>2^{g+1}(D(j+3)-C),\quad
U2^j\ge2^{g+1}D.
\]

These inequalities persist at all higher j, since the exponential gaps double while the linear term increases by D. If `a>=j-g`, the `3D2^a` term of (3) exceeds the target even after subtracting C. If `a<j-g`, the deficit is larger than the remaining linear correction. Hence no exceptional `v=3` source exists. This closes the complete inverse fiber without limiting the predecessor valuation or the target parameter.

Because `Y_k>10` and there are **no incoming first-even transitions** into `Y_k`, no positive-time segment of the genuine even orbit starting at 10 can reach it.

## Newness relative to explicit prior certificates

The theorem's progression has no intersection with the **28 previously listed** infinite first-even E inverse-cone progressions: four Agent14, five Agent16, twelve Agent22, and seven later Agent14 cases. For each earlier base/period pair `(J,P)`, the certificate checks the infinite-progression disjointness condition `(1296-J) mod gcd(340200,P) != 0`. Compare [Agent14/16 older families](../agent14-sheep-even-inverse/ROOT-FREE-CONES.md), [Agent22's twelve](../agent22-sheep-new-cones/README.md), and [Agent14's seven](../agent14-sheep-seven-cones/README.md). This establishes relative non-overlap only; broader external novelty is not established.

The prior ordinary-section F depth-five sieve excluded 3,596/5,400 residue classes of target exponents. The new progression evades that entire sieve. Because `3^5 | 2^j-1`, each target has the five **genuine ordinary F predecessors**

\[
z_i=1+2^i(2^j-1)/3^i,\quad i=1,\ldots,5,\qquad z_0=2^j,
\]

with `F(z_i)=z_(i-1)` and all intermediates odd, at least five. Since `340200` is a multiple of 5,400, the entire progression shares the same unexcluded F residue class. Its absence of *first-even* E ancestors is a stronger obstruction from complete hidden-odd excursions.

## Reproduction and status

- [certificate.py](certificate.py) checks all exact 3-adic, valuation, exceptional-source and prior-overlap conditions with Python 3.10+ standard library.
- [SheepPower1296Core.lean](SheepPower1296Core.lean), [SheepPower1296Rows.lean](SheepPower1296Rows.lean), and [SheepPower1296All.lean](SheepPower1296All.lean) compiled locally under **Lean 4.36.0-rc2**, with no `sorry`, `admit` or `native_decide`. The final generic exclusion audits exactly `[propext, Classical.choice, Quot.sound]`, and the all-index mod729 theorem audits `[propext, Quot.sound]`. [generate.py](generate.py) deterministically recreates the 41 row statements using locked, atomic file replacement.
- The original Turing-machine to E-section correspondence is covered by Agent16's existing source CI. The new three Lean arithmetic modules have **not yet been composed into a fresh complete source-importing machine-level theorem**. The mathematical composition above uses those established section semantics.

This belongs in **`im-results/`** because one thin arithmetic progression of excluded halting exponents does not decide this holdout, does not strengthen the global six-state Busy Beaver lower bound, and has not undergone an external novelty review. The remaining task is an authentic all-exponent blank-root exclusion or a genuine halting witness.
