# Complementary valuation-three parents at Sheep power gates

**Scope and status.** An all-exponent paper theorem for the exact published Sheep first-even return map, strengthened by a standalone Lean 4.36.0-rc2 kernel certificate for the complete modulo-17 iff and arithmetic source construction, plus an independent exact-integer verifier. The all-\(k\) 3-adic valuation and source-to-return composition are proved below in ordinary mathematics; they are **not yet combined into one original-source Lean theorem**. The existing source-to-section semantic connection is separately checked by Agent16. The constructed parents are legal *synthetic* sources and have **no known blank-tape reachability**. This result neither decides Sheep nor determines BB(6). External novelty and independent peer review remain open. Keep under \`im-results/\`.

Machine: \`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE\`. Let \`F\` denote its published nonterminal section return; for an even legal source \`x=2^a*v\`, with \`a>=1\` and odd \`v>=5\`,
\[
F(x)=2^a v+a+(v-1)/2.
\]
If \`F(x)-1=2^h q\` with \`q\` odd, then the *genuine first-even section return* is \`E(x)=1+3^h q\`. Agent16 already linked this E relation to the original machine in [source CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

## Theorem: exact additional valuation-three family

For every integer \`k>=1\`, set \`j=2*3^k\`, \`Y=2^j\`, and \`H=k+1\`. Every legal generic **source with valuation exactly three**, \`x=8v\`, \`v>=5\` odd, and \`E(x)=Y\` with \`h>=1\` hidden odd steps arises as
\[
q_h=(2^j-1)/3^h,\qquad
v_h=(2^{h+1}q_h-3)/17,\qquad x_h=8v_h,
\]
for a unique \`h\` satisfying exactly
\[
1\le h\le k+1,\qquad
\begin{cases}
h\equiv10\pmod{16},&k\text{ even},\\
h\equiv14\pmod{16},&k\text{ odd}.
\end{cases}
\]
Conversely **every** such \`h\` gives an odd integer \`v_h>=5\`, and \`E(x_h)=Y\` with precisely \`h\` hidden odd steps. These sources are distinct and have exact two-adic valuation three.

The full set of valuation-three parents in this sector is given by this theorem: \`h=0\` is impossible for these even exponents by the independent high-valuation signed-power gap already proved in [UNIFORM-VALUATION.md](../agent17-sheep-geometric-rays/UNIFORM-VALUATION.md); the exceptional valuation-three source \`x=24\` returns \`E(24)=30\`, never a power.

The number \`A(k)\` of additional valuation-three parents is
\[
A(k)=
\begin{cases}
0,&k\text{ even},\ k<10,\\
1+\lfloor(k-10)/16\rfloor,&k\text{ even},\ k\ge10,\\
0,&k\text{ odd},\ k<13,\\
1+\lfloor(k-13)/16\rfloor,&k\text{ odd},\ k\ge13.
\end{cases}
\]
Agent17's earlier [valuation-one theorem](../agent17-sheep-geometric-rays/UNBOUNDED-POWER-FANIN.md) already supplies exactly \`B(k)=ceil((k+1)/2)\` distinct valuation-one legal parents of these same targets, via the odd \`h\` values. Since the new parents have valuation three, these families are disjoint. Therefore
\[
\operatorname{indegree}_E(2^{2\cdot3^k})
\ \ge\ \lceil(k+1)/2\rceil+A(k),
\qquad
\liminf_{k\longrightarrow\infty}
\frac{\operatorname{indegree}_E(2^{2\cdot3^k})}{k}\ \ge\frac9{16}.
\]
This improves the earlier directly exhibited slope \`1/2\` for the same sequence of targets. It does not claim the lower bound is the exact indegree, since other valuations can contribute.

## Proof

**Exact odd-block bound and positive cofactor.** The elementary identity \`v3(2^(2*3^k)-1)=k+1\` follows by induction: writing \`U=4^(3^k)=1+3s\`, one has
\[
U^2+U+1=3(1+3s+3s^2),
\]
whose remaining factor is \`1 mod 3\`; the factorization \`U^3-1=(U-1)(U^2+U+1)\` increases the 3-adic valuation by one at each step. Thus \`3^h|(2^j-1)\` iff \`h<=k+1\`. The minimum cofactor \`Q_k=(2^(2*3^k)-1)/3^(k+1)\` is \`Q_1=7\`, and the factorization gives \`Q_(k+1)=Q_k*(U^2+U+1)/3 >= Q_k\`. Therefore every admissible \`q_h\` is odd and at least seven.

**Source equation.** For \`x=8v\`, the exact generic return is \`F(8v)=(17v+5)/2\`. Hence \`F(x)-1=2^h q_h\` is equivalent to
\[
17v+3=2^{h+1}q_h.\tag{A}
\]
Such \`v\` is integral iff \`2^(h+1)q_h=3 mod17\`. Reducing \`3^h q_h=2^j-1\` modulo 17 yields the equivalent condition
\[
3^{h+1}=2^{h+1}(2^j-1)\pmod{17}.\tag{B}
\]
The element 3 has order 16 modulo 17, as does 2. For \`k=2s\`, \`2^j=4^(9^s)=4 mod17\`, so (B) is \`3^(h+1)=3*2^(h+1) mod17\`; direct exact enumeration of all 16 possible residues \`h mod16\` gives only \`h=10 mod16\`. For \`k=2s+1\`, \`2^j=4^(3*9^s)=13 mod17\`, making (B) \`3^(h+1)=12*2^(h+1) mod17\`; the unique solution is \`h=14 mod16\`. [SheepA3Boost.lean](SheepA3Boost.lean) certifies the **complete all-natural iff**, including both implications, without testing finitely many target exponents.

**Sufficiency and legality.** For each prescribed \`h\`, equation (B) makes \`v_h\` integral. The numerator \`2^(h+1)q_h-3\` is odd, so \`v_h\` is odd. The smallest allowed \`h\` is 10 and \`q_h>=7\`, giving \`v_h>=5\`. Equation (A) reconstructs \`F(x_h)-1=2^h q_h\`; since \`q_h\` is odd the hidden length is *exactly* \`h\`. Therefore \`E(x_h)=1+3^h q_h=2^j\`. Distinct \`h\` yield distinct \`v_h\` because \`2^(h+1)q_h=2*(2/3)^h(2^j-1)\` strictly decreases as \`h\` increases. Counting the two progressions proves \`A(k)\`, then combining with the previously established valuation-one family proves the indegree bound.

## Reproducibility and remaining proof boundary

- [SheepA3Boost.lean](SheepA3Boost.lean): standalone Lean 4.36.0-rc2 source, \`import Std\`. Locally compiled successfully. \`#print axioms\` for \`mod_iff_even\`, \`mod_iff_odd\`, \`parent_arithmetic\`, \`parent_even\`, and \`parent_odd\` returned exactly \`[propext, Quot.sound]\`; no admitted theorem or nonstandard axiom. The final two parent theorems take the explicit \`3^h*q+1=2^j\` identity and the proven elementary \`q>=7\` as hypotheses. They establish the requisite odd legal source and exact algebraic transition equation. Source-machine imports and the all-k valuation induction are separate obligations if a unified original-machine theorem is desired.
- [a3_boost_verify.py](a3_boost_verify.py): pure Python 3. The exact modular verifier tested all \`k=1..128\`, all \`h=1..k+1\` (8,384 cases), reproducing the necessary-and-sufficient classes. Three small complete big-integer source reconstructions checked the literal \`F\` and \`E\` transitions, yielding SHA256 of concatenated individual source digests \`d4c0e2af63be390312512e00e6ffd509404176fcdfe80ea267c34bae68246ae9\`. These finite checks corroborate the all-parameter derivation; they are not substituted for it.

**Prior-art distinction.** The preexisting [A3-POWER-FANIN.md](../agent17-sheep-geometric-rays/A3-POWER-FANIN.md) concerns exponent \`j=4*3^k\`, source valuation three, and hidden lengths \`h=1 mod16\`. That target sequence has \`j=4 mod8\`. The present theorem concerns the disjoint sequence \`j=2*3^k\`, with exponents \`j=2 mod4\`, and combines new valuation-three sources with earlier valuation-one sources. No new blank-root machine classification follows.

**Next useful step:** import this source arithmetic into Agent16's exact E definitions and then seek a root-sensitive theorem excluding all surviving halting powers. Further synthetic-parent counting alone cannot decide the machine.
